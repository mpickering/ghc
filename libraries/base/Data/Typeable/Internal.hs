{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Typeable.Internal
-- Copyright   :  (c) The University of Glasgow, CWI 2001--2011
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- The representations of the types TyCon and TypeRep, and the
-- function mkTyCon which is used by derived instances of Typeable to
-- construct a TyCon.
--
-----------------------------------------------------------------------------

module Data.Typeable.Internal (
    Fingerprint(..),

    -- * Typeable class
    Typeable(..),
    withTypeable,

    -- * Module
    Module,  -- Abstract
    moduleName, modulePackage,

    -- * TyCon
    TyCon,   -- Abstract
    tyConPackage, tyConModule, tyConName,
    rnfTyCon,

    -- * TypeRep
    TypeRep,
    pattern TRApp, pattern TRCon, pattern TRFun,
    typeRep,
    typeOf,
    typeRepTyCon,
    typeRepKind,
    typeRepFingerprint,
    decomposeFun,
    splitApp,
    rnfTypeRep,
    eqTypeRep,

    -- * TypeRepX
    TypeRepX(..),
    typeRepX,
    typeRepXTyCon,
    typeRepXFingerprint,
    rnfTypeRepX,

    -- * Construction
    -- | These are for internal use only
    mkTrCon, mkTrApp, mkTyCon, mkTyCon#,
    typeSymbolTypeRep, typeNatTypeRep,

    -- * Representations for primitive types
    trTYPE,
    trTYPE'PtrRepLifted,
    trRuntimeRep,
    tr'PtrRepLifted,
    trArrow,
  ) where

import GHC.Base
import GHC.Types (TYPE)
import Data.Type.Equality
import GHC.Word
import GHC.Show
import GHC.TypeLits( KnownNat, KnownSymbol, natVal', symbolVal' )

import GHC.Fingerprint.Type
import {-# SOURCE #-} GHC.Fingerprint
   -- loop: GHC.Fingerprint -> Foreign.Ptr -> Data.Typeable
   -- Better to break the loop here, because we want non-SOURCE imports
   -- of Data.Typeable as much as possible so we can optimise the derived
   -- instances.

#include "MachDeps.h"

{- *********************************************************************
*                                                                      *
                The TyCon type
*                                                                      *
********************************************************************* -}

modulePackage :: Module -> String
modulePackage (Module p _) = trNameString p

moduleName :: Module -> String
moduleName (Module _ m) = trNameString m

tyConPackage :: TyCon -> String
tyConPackage (TyCon _ _ m _) = modulePackage m

tyConModule :: TyCon -> String
tyConModule (TyCon _ _ m _) = moduleName m

tyConName :: TyCon -> String
tyConName (TyCon _ _ _ n) = trNameString n

trNameString :: TrName -> String
trNameString (TrNameS s) = unpackCString# s
trNameString (TrNameD s) = s

tyConFingerprint :: TyCon -> Fingerprint
tyConFingerprint (TyCon hi lo _ _)
  = Fingerprint (W64# hi) (W64# lo)

-- | Helper to fully evaluate 'TyCon' for use as @NFData(rnf)@ implementation
--
-- @since 4.8.0.0
rnfModule :: Module -> ()
rnfModule (Module p m) = rnfTrName p `seq` rnfTrName m

rnfTrName :: TrName -> ()
rnfTrName (TrNameS _) = ()
rnfTrName (TrNameD n) = rnfString n

rnfTyCon :: TyCon -> ()
rnfTyCon (TyCon _ _ m n) = rnfModule m `seq` rnfTrName n

rnfString :: [Char] -> ()
rnfString [] = ()
rnfString (c:cs) = c `seq` rnfString cs


{- *********************************************************************
*                                                                      *
                The TypeRep type
*                                                                      *
********************************************************************* -}

-- | A concrete representation of a (monomorphic) type.
-- 'TypeRep' supports reasonably efficient equality.
data TypeRep (a :: k) where
    TrTyCon :: !Fingerprint -> !TyCon -> TypeRep k -> TypeRep (a :: k)
    TrApp   :: forall k1 k2 (a :: k1 -> k2) (b :: k1).
               !Fingerprint
            -> TypeRep (a :: k1 -> k2)
            -> TypeRep (b :: k1)
            -> TypeRep (a b)

on :: (a -> a -> r) -> (b -> a) -> (b -> b -> r)
on f g = \ x y -> g x `f` g y

-- Compare keys for equality

-- | @since 2.01
instance Eq (TypeRep a) where
  (==) = (==) `on` typeRepFingerprint

-- | @since 4.4.0.0
instance Ord (TypeRep a) where
  compare = compare `on` typeRepFingerprint

-- | A non-indexed type representation.
data TypeRepX where
    TypeRepX :: TypeRep a -> TypeRepX

instance Eq TypeRepX where
  TypeRepX a == TypeRepX b =
      case a `eqTypeRep` b of
          Just _  -> True
          Nothing -> False

instance Ord TypeRepX where
  TypeRepX a `compare` TypeRepX b =
    typeRepFingerprint a `compare` typeRepFingerprint b

pattern TRFun :: forall fun. ()
              => forall arg res. (fun ~ (arg -> res))
              => TypeRep arg
              -> TypeRep res
              -> TypeRep fun
pattern TRFun arg res <- TrApp _ (TrApp _ (eqTypeRep trArrow -> Just HRefl) arg) res

decomposeFun :: forall fun r.
                TypeRep fun
             -> r
             -> (forall arg res. (fun ~ (arg -> res)) => TypeRep arg -> TypeRep res -> r)
             -> r
decomposeFun (TrApp _ (TrApp _ arr r1) r2) _def cont
  | Just HRefl <- arr `eqTypeRep` trArrow
  = cont r1 r2
decomposeFun _ def _
  = def

-- | Observe the 'Fingerprint' of a type representation
--
-- @since 4.8.0.0
typeRepFingerprint :: TypeRep a -> Fingerprint
typeRepFingerprint (TrTyCon fpr _ _) = fpr
typeRepFingerprint (TrApp fpr _ _) = fpr

-- | Construct a representation for a type constructor
-- applied at a monomorphic kind.
--
-- Note that this is unsafe as it allows you to construct
-- ill-kinded types.
mkTrCon :: forall k (a :: k). TyCon -> TypeRep k -> TypeRep a
mkTrCon tc kind = TrTyCon fpr tc kind
  where
    fpr_tc = tyConFingerprint tc
    fpr_k  = typeRepFingerprint kind
    fpr    = fingerprintFingerprints [fpr_tc, fpr_k]

-- | Construct a representation for a type application.
-- TODO: Is this necessary?
mkTrApp :: forall k1 k2 (a :: k1 -> k2) (b :: k1).
           TypeRep (a :: k1 -> k2)
        -> TypeRep (b :: k1)
        -> TypeRep (a b)
mkTrApp a b = TrApp fpr a b
  where
    fpr_a = typeRepFingerprint a
    fpr_b = typeRepFingerprint b
    fpr   = fingerprintFingerprints [fpr_a, fpr_b]


data AppResult (t :: k) where
    App :: TypeRep a -> TypeRep b -> AppResult (a b)

-- | Pattern match on a type application
pattern TRApp :: forall k2 (fun :: k2). ()
              => forall k1 (a :: k1 -> k2) (b :: k1). (fun ~ a b)
              => TypeRep a -> TypeRep b -> TypeRep fun
pattern TRApp f x <- TrApp _ f x

withTypeable :: TypeRep a -> (Typeable a => b) -> b
withTypeable = undefined

-- | Pattern match on a type constructor
-- TODO: do we want to expose kinds in these patterns?
pattern TRCon :: forall k (a :: k). TyCon -> TypeRep a
pattern TRCon con <- TrTyCon _ con _

-- | Splits a type application.
splitApp :: TypeRep a -> Maybe (AppResult a)
splitApp (TrTyCon _ _ _) = Nothing
splitApp (TrApp _ f x)   = Just $ App f x

----------------- Observation ---------------------

typeRepKind :: forall k (a :: k). TypeRep a -> TypeRep k
typeRepKind (TrTyCon _ _ k) = k
typeRepKind (TrApp _ f _) =
    case typeRepKind f of
        TRFun _arg res -> res
        _              -> error "typeRepKind: impossible"

-- | Observe the type constructor of a quantified type representation.
typeRepXTyCon :: TypeRepX -> TyCon
typeRepXTyCon (TypeRepX t) = typeRepTyCon t

-- | Observe the type constructor of a type representation
typeRepTyCon :: TypeRep a -> TyCon
typeRepTyCon (TrTyCon _ tc _) = tc
typeRepTyCon (TrApp _ a _)    = typeRepTyCon a

-- | Type equality
--
-- @since TODO
eqTypeRep :: forall k1 k2 (a :: k1) (b :: k2).
             TypeRep a -> TypeRep b -> Maybe (a :~~: b)
eqTypeRep a b
  | typeRepFingerprint a == typeRepFingerprint b = Just (unsafeCoerce# HRefl)
  | otherwise                                    = Nothing

{- *********************************************************************
*                                                                      *
                The Typeable class
*                                                                      *
********************************************************************* -}

-------------------------------------------------------------
--
--      The Typeable class and friends
--
-------------------------------------------------------------

-- | The class 'Typeable' allows a concrete representation of a type to
-- be calculated.
class Typeable a where
  typeRep# :: TypeRep a

typeRep :: Typeable a => TypeRep a
typeRep = typeRep#

typeOf :: Typeable a => a -> TypeRep a
typeOf _ = typeRep

-- | Takes a value of type @a@ and returns a concrete representation
-- of that type.
--
-- @since 4.7.0.0
typeRepX :: forall proxy a. Typeable a => proxy a -> TypeRepX
typeRepX _ = TypeRepX (typeRep :: TypeRep a)
{-# INLINE typeRep #-}

typeRepXFingerprint :: TypeRepX -> Fingerprint
typeRepXFingerprint (TypeRepX t) = typeRepFingerprint t

----------------- Showing TypeReps --------------------

instance Show (TypeRep (a :: k)) where
  showsPrec _ rep
    | isListTyCon tc, [ty] <- tys =
      showChar '[' . shows ty . showChar ']'
    | isTupleTyCon tc =
      showChar '(' . showArgs (showChar ',') tys . showChar ')'
    where (tc, tys) = splitApps rep
  showsPrec p (TrTyCon _ tycon _) = showsPrec p tycon
  --showsPrec p (TRFun x r) =
  --    showParen (p > 8) $
  --    showsPrec 9 x . showString " -> " . showsPrec 8 r
  showsPrec p (TrApp _ (TrApp _ (TrTyCon _ tycon _) x) r)
    | isArrowTyCon tycon =
      showParen (p > 8) $
      showsPrec 9 x . showString " -> " . showsPrec p r

  showsPrec p (TrApp _ f x)
    | otherwise =
      showParen (p > 9) $
      showsPrec 8 f .
      showChar ' ' .
      showsPrec 9 x

-- | @since 4.10.0.0
instance Show TypeRepX where
  showsPrec p (TypeRepX ty) = showsPrec p ty

splitApps :: TypeRep a -> (TyCon, [TypeRepX])
splitApps = go []
  where
    go :: [TypeRepX] -> TypeRep a -> (TyCon, [TypeRepX])
    go xs (TrTyCon _ tc _) = (tc, xs)
    go xs (TrApp _ f x)    = go (TypeRepX x : xs) f

isArrowTyCon :: TyCon -> Bool
isArrowTyCon tc = tc == typeRepTyCon (typeRep :: TypeRep (->))

isListTyCon :: TyCon -> Bool
isListTyCon tc = tc == typeRepTyCon (typeRep :: TypeRep [Int])

isTupleTyCon :: TyCon -> Bool
isTupleTyCon tc
  | ('(':',':_) <- tyConName tc = True
  | otherwise                   = False

showArgs :: Show a => ShowS -> [a] -> ShowS
showArgs _   []     = id
showArgs _   [a]    = showsPrec 10 a
showArgs sep (a:as) = showsPrec 10 a . sep . showArgs sep as

-- | Helper to fully evaluate 'TypeRep' for use as @NFData(rnf)@ implementation
--
-- @since 4.8.0.0
rnfTypeRep :: TypeRep a -> ()
rnfTypeRep (TrTyCon _ tyc _) = rnfTyCon tyc
rnfTypeRep (TrApp _ f x)     = rnfTypeRep f `seq` rnfTypeRep x

-- | Helper to fully evaluate 'TypeRepX' for use as @NFData(rnf)@ implementation
--
-- @since 4.10.0.0
rnfTypeRepX :: TypeRepX -> ()
rnfTypeRepX (TypeRepX r) = rnfTypeRep r

{- *********************************************************
*                                                          *
*       TyCon/TypeRep definitions for type literals        *
*              (Symbol and Nat)                            *
*                                                          *
********************************************************* -}

-- | Exquisitely unsafe.
mkTyCon# :: Addr#       -- ^ package name
         -> Addr#       -- ^ module name
         -> Addr#       -- ^ the name of the type constructor
         -> TyCon       -- ^ A unique 'TyCon' object
mkTyCon# pkg modl name
  | Fingerprint (W64# hi) (W64# lo) <- fingerprint
  = TyCon hi lo (Module (TrNameS pkg) (TrNameS modl)) (TrNameS name)
  where
    fingerprint :: Fingerprint
    fingerprint = fingerprintString (unpackCString# pkg
                                    ++ (' ': unpackCString# modl)
                                    ++ (' ' : unpackCString# name))
-- it is extremely important that this fingerprint computation
-- remains in sync with that in TcTypeable to ensure that type
-- equality is correct.

-- | Exquisitely unsafe.
mkTyCon :: String       -- ^ package name
        -> String       -- ^ module name
        -> String       -- ^ the name of the type constructor
        -> TyCon        -- ^ A unique 'TyCon' object
-- Used when the strings are dynamically allocated,
-- eg from binary deserialisation
mkTyCon pkg modl name
  | Fingerprint (W64# hi) (W64# lo) <- fingerprint
  = TyCon hi lo (Module (TrNameD pkg) (TrNameD modl)) (TrNameD name)
  where
    fingerprint :: Fingerprint
    fingerprint = fingerprintString (pkg ++ (' ':modl) ++ (' ':name))

mkTypeLitTyCon :: String -> TyCon
mkTypeLitTyCon name = mkTyCon "base" "GHC.TypeLits" name

-- | Used to make `'Typeable' instance for things of kind Nat
typeNatTypeRep :: KnownNat a => Proxy# a -> TypeRep a
typeNatTypeRep p = typeLitTypeRep (show (natVal' p))

-- | Used to make `'Typeable' instance for things of kind Symbol
typeSymbolTypeRep :: KnownSymbol a => Proxy# a -> TypeRep a
typeSymbolTypeRep p = typeLitTypeRep (show (symbolVal' p))

-- | An internal function, to make representations for type literals.
typeLitTypeRep :: forall (a :: k). (Typeable k) => String -> TypeRep a
typeLitTypeRep nm = mkTrCon (mkTypeLitTyCon nm) typeRep

{- *********************************************************
*                                                          *
*       TyCon/TypeRep definitions for primitive types      *
*       (TYPE, RuntimeRep, (->) and promoted constructors) *
*                                                          *
********************************************************* -}

{-
Note [Mutually recursive representations of primitive types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

These primitive types exhibit mutual recursion through their kinds.

    TYPE          :: RuntimeRep -> TYPE 'PtrRepLifted
    RuntimeRep    :: TYPE 'PtrRepLifted
    'PtrRepLifted :: RuntimeRep
    (->)          :: TYPE 'PtrRepLifted -> TYPE 'PtrRepLifted -> Type 'PtrRepLifted
    TYPE 'PtrRepLifted :: TYPE 'PtrRepLifted

For this reason we are forced to define their representations
manually.
-}

-- | We can't use 'mkTrCon' here as it requires the fingerprint of the kind
-- which is knot-tied.
mkPrimTrCon :: forall k (a :: k). TyCon -> TypeRep k -> TypeRep a
mkPrimTrCon tc kind = TrTyCon fpr tc kind
  where
    fpr_tc  = tyConFingerprint tc
    fpr_tag = fingerprintString "prim"
    fpr     = fingerprintFingerprints [fpr_tag, fpr_tc]

mkPrimTyCon :: String -> TyCon
mkPrimTyCon = mkTyCon "ghc-prim" "GHC.Prim"

trTYPE :: TypeRep TYPE
trTYPE = mkPrimTrCon (mkPrimTyCon "TYPE") runtimeRep_arr_type
  where
    runtimeRep_arr :: TypeRep ((->) RuntimeRep)
    runtimeRep_arr = mkTrApp trArrow trRuntimeRep

    runtimeRep_arr_type :: TypeRep ((->) RuntimeRep (TYPE 'PtrRepLifted))
    runtimeRep_arr_type = mkTrApp runtimeRep_arr star

trRuntimeRep :: TypeRep RuntimeRep
trRuntimeRep = mkPrimTrCon (mkPrimTyCon "RuntimeRep") star

tr'PtrRepLifted :: TypeRep 'PtrRepLifted
tr'PtrRepLifted = mkPrimTrCon (mkPrimTyCon "'PtrRepLifted") trRuntimeRep

trTYPE'PtrRepLifted :: TypeRep (TYPE 'PtrRepLifted)
trTYPE'PtrRepLifted = mkTrApp trTYPE tr'PtrRepLifted

trArrowTyCon :: TyCon
trArrowTyCon = mkPrimTyCon "->"

trArrow :: TypeRep (->)
trArrow = mkPrimTrCon trArrowTyCon star_arr_star_arr_star

-- Some useful aliases
star :: TypeRep (TYPE 'PtrRepLifted)
star = trTYPE'PtrRepLifted

star_arr :: TypeRep ((->) * :: * -> *)
star_arr = mkTrApp trArrow star

star_arr_star :: TypeRep (* -> * :: *)
star_arr_star = mkTrApp star_arr star

star_arr_star_arr_star :: TypeRep (* -> * -> *)
star_arr_star_arr_star = mkTrApp star_arr star_arr_star
