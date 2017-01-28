{-# LANGUAGE AllowAmbiguousTypes #-}
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
    tyConPackage, tyConModule, tyConName, tyConKindVars, tyConKindRep,
    KindRep(..),
    rnfTyCon,

    -- * TypeRep
    TypeRep,
    pattern TRApp, pattern TRCon, pattern TRCon', pattern TRFun,
    typeRep,
    typeOf,
    typeRepTyCon,
    typeRepFingerprint,
    splitApp,
    rnfTypeRep,
    eqTypeRep,
    typeRepKind,

    -- * SomeTypeRep
    SomeTypeRep(..),
    typeRepX,
    typeRepXTyCon,
    typeRepXFingerprint,
    rnfSomeTypeRep,

    -- * Construction
    -- | These are for internal use only
    mkTrCon, mkTrApp, mkTyCon, mkTyCon#,
    typeSymbolTypeRep, typeNatTypeRep,
  ) where

import GHC.Base
import qualified GHC.Arr as A
import GHC.Types (TYPE)
import Data.Type.Equality
import GHC.Word
import GHC.Show
import GHC.TypeLits( KnownNat, KnownSymbol, natVal', symbolVal' )
import Unsafe.Coerce

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
tyConPackage (TyCon _ _ m _ _ _) = modulePackage m

tyConModule :: TyCon -> String
tyConModule (TyCon _ _ m _ _ _) = moduleName m

tyConName :: TyCon -> String
tyConName (TyCon _ _ _ n _ _) = trNameString n

trNameString :: TrName -> String
trNameString (TrNameS s) = unpackCString# s
trNameString (TrNameD s) = s

tyConFingerprint :: TyCon -> Fingerprint
tyConFingerprint (TyCon hi lo _ _ _ _)
  = Fingerprint (W64# hi) (W64# lo)

tyConKindVars :: TyCon -> Int
tyConKindVars (TyCon _ _ _ _ n _) = I# n

tyConKindRep :: TyCon -> KindRep
tyConKindRep (TyCon _ _ _ _ _ k) = k

-- | Helper to fully evaluate 'TyCon' for use as @NFData(rnf)@ implementation
--
-- @since 4.8.0.0
rnfModule :: Module -> ()
rnfModule (Module p m) = rnfTrName p `seq` rnfTrName m

rnfTrName :: TrName -> ()
rnfTrName (TrNameS _) = ()
rnfTrName (TrNameD n) = rnfString n

rnfKindRep :: KindRep -> ()
rnfKindRep (KindRepTyConApp tc args) = rnfTyCon tc `seq` rnfList rnfKindRep args
rnfKindRep (KindRepVar _)   = ()
rnfKindRep (KindRepApp a b) = rnfKindRep a `seq` rnfKindRep b
rnfKindRep (KindRepFun a b) = rnfKindRep a `seq` rnfKindRep b
rnfKindRep (KindRepTYPE rr) = rnfRuntimeRep rr

rnfRuntimeRep :: RuntimeRep -> ()
rnfRuntimeRep (VecRep !_ !_) = ()
rnfRuntimeRep !_             = ()

rnfList :: (a -> ()) -> [a] -> ()
rnfList _     []     = ()
rnfList force (x:xs) = force x `seq` rnfList force xs

rnfString :: [Char] -> ()
rnfString = rnfList (`seq` ())

rnfTyCon :: TyCon -> ()
rnfTyCon (TyCon _ _ m n _ k) = rnfModule m `seq` rnfTrName n `seq` rnfKindRep k


{- *********************************************************************
*                                                                      *
                The TypeRep type
*                                                                      *
********************************************************************* -}

-- | A concrete representation of a (monomorphic) type.
-- 'TypeRep' supports reasonably efficient equality.
data TypeRep (a :: k) where
    TrTyCon :: {-# UNPACK #-} !Fingerprint -> !TyCon -> [SomeTypeRep] -> TypeRep (a :: k)
    TrApp   :: forall k1 k2 (a :: k1 -> k2) (b :: k1).
               {-# UNPACK #-} !Fingerprint
            -> TypeRep (a :: k1 -> k2)
            -> TypeRep (b :: k1)
            -> TypeRep (a b)
    TrFun   :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep) (a :: TYPE r1) (b :: TYPE r2).
               {-# UNPACK #-} !Fingerprint
            -> TypeRep a
            -> TypeRep b
            -> TypeRep (a -> b)

on :: (a -> a -> r) -> (b -> a) -> (b -> b -> r)
on f g = \ x y -> g x `f` g y

-- Compare keys for equality

-- | @since 2.01
instance Eq (TypeRep a) where
  (==) = (==) `on` typeRepFingerprint

instance TestEquality TypeRep where
  testEquality a b
    | typeRepFingerprint a == typeRepFingerprint b = Just (unsafeCoerce# Refl)
    | otherwise                                    = Nothing

-- | @since 4.4.0.0
instance Ord (TypeRep a) where
  compare = compare `on` typeRepFingerprint

-- | A non-indexed type representation.
data SomeTypeRep where
    SomeTypeRep :: forall k (a :: k). TypeRep a -> SomeTypeRep

instance Eq SomeTypeRep where
  SomeTypeRep a == SomeTypeRep b =
      case a `eqTypeRep` b of
          Just _  -> True
          Nothing -> False

instance Ord SomeTypeRep where
  SomeTypeRep a `compare` SomeTypeRep b =
    typeRepFingerprint a `compare` typeRepFingerprint b

pattern TRFun :: forall k (fun :: k). ()
              => forall (r1 :: RuntimeRep) (r2 :: RuntimeRep) (arg :: TYPE r1) (res :: TYPE r2). (k ~ Type, fun ~~ (arg -> res))
              => TypeRep arg
              -> TypeRep res
              -> TypeRep fun
pattern TRFun arg res <- TrFun _ arg res
  where TRFun arg res = mkTrFun arg res

-- | Observe the 'Fingerprint' of a type representation
--
-- @since 4.8.0.0
typeRepFingerprint :: TypeRep a -> Fingerprint
typeRepFingerprint (TrTyCon fpr _ _) = fpr
typeRepFingerprint (TrApp fpr _ _) = fpr
typeRepFingerprint (TrFun fpr _ _) = fpr

-- | Construct a representation for a type constructor
-- applied at a monomorphic kind.
--
-- Note that this is unsafe as it allows you to construct
-- ill-kinded types.
mkTrCon :: forall k (a :: k). TyCon -> [SomeTypeRep] -> TypeRep a
mkTrCon tc kind_vars = TrTyCon fpr tc kind_vars
  where
    fpr_tc  = tyConFingerprint tc
    fpr_kvs = map typeRepXFingerprint kind_vars
    fpr     = fingerprintFingerprints (fpr_tc:fpr_kvs)

-- | Construct a representation for a type application.
--
-- Note that this is known-key to the compiler, which uses it in desugar
-- 'Typeable' evidence.
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
pattern TRApp :: forall k2 (t :: k2). ()
              => forall k1 (a :: k1 -> k2) (b :: k1). (t ~ a b)
              => TypeRep a -> TypeRep b -> TypeRep t
pattern TRApp f x <- TrApp _ f x
  where TRApp f x = mkTrApp f x

-- | Use a 'TypeRep' as 'Typeable' evidence.
withTypeable :: forall a r. TypeRep a -> (Typeable a => r) -> r
withTypeable rep k = unsafeCoerce k' rep
  where k' :: Gift a r
        k' = Gift k

-- | A helper to satisfy the type checker in 'withTypeable'.
newtype Gift a r = Gift (Typeable a => r)

-- | Pattern match on a type constructor
pattern TRCon :: forall k (a :: k). TyCon -> TypeRep a
pattern TRCon con <- TrTyCon _ con _

-- | Pattern match on a type constructor including its instantiated kind
-- variables.
pattern TRCon' :: forall k (a :: k). TyCon -> [SomeTypeRep] -> TypeRep a
pattern TRCon' con ks <- TrTyCon _ con ks

-- | Splits a type application.
splitApp :: TypeRep a -> Maybe (AppResult a)
splitApp (TrTyCon _ _ _) = Nothing
splitApp (TrApp _ f x)   = Just $ App f x
splitApp (TrFun _ _ _)   = Nothing

----------------- Observation ---------------------

-- | Observe the type constructor of a quantified type representation.
typeRepXTyCon :: SomeTypeRep -> TyCon
typeRepXTyCon (SomeTypeRep t) = typeRepTyCon t

-- | Observe the type constructor of a type representation
typeRepTyCon :: TypeRep a -> TyCon
typeRepTyCon (TrTyCon _ tc _) = tc
typeRepTyCon (TrApp _ a _)    = typeRepTyCon a
typeRepTyCon (TrFun _ _ _)    = error "typeRepTyCon: FunTy" -- TODO

-- | Type equality
--
-- @since TODO
eqTypeRep :: forall k1 k2 (a :: k1) (b :: k2).
             TypeRep a -> TypeRep b -> Maybe (a :~~: b)
eqTypeRep a b
  | typeRepFingerprint a == typeRepFingerprint b = Just (unsafeCoerce# HRefl)
  | otherwise                                    = Nothing


-------------------------------------------------------------
--
--      Computing kinds
--
-------------------------------------------------------------

-- | Observe the kind of a type.
typeRepKind :: TypeRep (a :: k) -> TypeRep k
typeRepKind (TrTyCon _ tc args)
  = unsafeCoerceRep $ tyConKind tc args
typeRepKind (TrApp _ f _)
  | TRFun _ res <- typeRepKind f
  = res
typeRepKind (TrFun _ _ _) = typeRep @Type
typeRepKind _ = error "Ill-kinded type representation"

tyConKind :: TyCon ->  [SomeTypeRep] -> SomeTypeRep
tyConKind (TyCon _ _ _ _ nKindVars# kindRep) kindVars = go kindRep
  where
    nKindVars = I# nKindVars#
    kindVarsArr :: A.Array KindBndr SomeTypeRep
    kindVarsArr = A.listArray (0,nKindVars) kindVars

    go :: KindRep -> SomeTypeRep
    go (KindRepTyConApp tc args) = undefined -- tyConKind tc args
    go (KindRepVar var) = kindVarsArr A.! var
    go (KindRepApp f a)
      = SomeTypeRep $ TRApp (unsafeCoerceRep $ go f) (unsafeCoerceRep $ go a)
    go (KindRepFun a b)
      = SomeTypeRep $ TRFun (unsafeCoerceRep $ go a) (unsafeCoerceRep $ go b)
    go (KindRepTYPE r) = unkindedTypeRep $ runtimeRepTypeRep r

unsafeCoerceRep :: SomeTypeRep -> TypeRep a
unsafeCoerceRep (SomeTypeRep r) = unsafeCoerce r

unkindedTypeRep :: SomeKindedTypeRep k -> SomeTypeRep
unkindedTypeRep (SomeKindedTypeRep x) = SomeTypeRep x

data SomeKindedTypeRep k where
    SomeKindedTypeRep :: forall (a :: k). TypeRep a -> SomeKindedTypeRep k

kApp :: SomeKindedTypeRep (k -> k') -> SomeKindedTypeRep k -> SomeKindedTypeRep k'
kApp (SomeKindedTypeRep f) (SomeKindedTypeRep a) = SomeKindedTypeRep (TRApp f a)

kindedTypeRep :: forall (a :: k). Typeable a => SomeKindedTypeRep k
kindedTypeRep = SomeKindedTypeRep (typeRep @a)

buildList :: forall k. Typeable k => [SomeKindedTypeRep k] -> SomeKindedTypeRep [k]
buildList = foldr cons nil
  where
    nil = kindedTypeRep @[k] @'[]
    cons x rest = SomeKindedTypeRep (typeRep @'(:)) `kApp` x `kApp` rest

runtimeRepTypeRep :: RuntimeRep -> SomeKindedTypeRep RuntimeRep
runtimeRepTypeRep r =
    case r of
      LiftedRep   -> rep @'LiftedRep
      UnliftedRep -> rep @'UnliftedRep
      VecRep c e  -> kindedTypeRep @_ @'VecRep
                     `kApp` vecCountTypeRep c
                     `kApp` vecElemTypeRep e
      TupleRep rs -> kindedTypeRep @_ @'TupleRep
                     `kApp` buildList (map runtimeRepTypeRep rs)
      SumRep rs   -> kindedTypeRep @_ @'SumRep
                     `kApp` buildList (map runtimeRepTypeRep rs)
      IntRep      -> rep @'IntRep
      WordRep     -> rep @'WordRep
      Int64Rep    -> rep @'Int64Rep
      Word64Rep   -> rep @'Word64Rep
      AddrRep     -> rep @'AddrRep
      FloatRep    -> rep @'FloatRep
      DoubleRep   -> rep @'DoubleRep
  where
    rep :: forall (a :: RuntimeRep). Typeable a => SomeKindedTypeRep RuntimeRep
    rep = kindedTypeRep @RuntimeRep @a

vecCountTypeRep :: VecCount -> SomeKindedTypeRep VecCount
vecCountTypeRep c =
    case c of
      Vec2  -> rep @'Vec2
      Vec4  -> rep @'Vec4
      Vec8  -> rep @'Vec8
      Vec16 -> rep @'Vec16
      Vec32 -> rep @'Vec32
      Vec64 -> rep @'Vec64
  where
    rep :: forall (a :: VecCount). Typeable a => SomeKindedTypeRep VecCount
    rep = kindedTypeRep @VecCount @a

vecElemTypeRep :: VecElem -> SomeKindedTypeRep VecElem
vecElemTypeRep e =
    case e of
      Int8ElemRep     -> rep @'Int8ElemRep
      Int16ElemRep    -> rep @'Int16ElemRep
      Int32ElemRep    -> rep @'Int32ElemRep
      Int64ElemRep    -> rep @'Int64ElemRep
      Word8ElemRep    -> rep @'Word8ElemRep
      Word16ElemRep   -> rep @'Word16ElemRep
      Word32ElemRep   -> rep @'Word32ElemRep
      Word64ElemRep   -> rep @'Word64ElemRep
      FloatElemRep    -> rep @'FloatElemRep
      DoubleElemRep   -> rep @'DoubleElemRep
  where
    rep :: forall (a :: VecElem). Typeable a => SomeKindedTypeRep VecElem
    rep = kindedTypeRep @VecElem @a

-------------------------------------------------------------
--
--      The Typeable class and friends
--
-------------------------------------------------------------

-- | The class 'Typeable' allows a concrete representation of a type to
-- be calculated.
class Typeable (a :: k) where
  typeRep# :: TypeRep a

typeRep :: Typeable a => TypeRep a
typeRep = typeRep#

typeOf :: Typeable a => a -> TypeRep a
typeOf _ = typeRep

-- | Takes a value of type @a@ and returns a concrete representation
-- of that type.
--
-- @since 4.7.0.0
typeRepX :: forall proxy a. Typeable a => proxy a -> SomeTypeRep
typeRepX _ = SomeTypeRep (typeRep :: TypeRep a)
{-# INLINE typeRep #-}

typeRepXFingerprint :: SomeTypeRep -> Fingerprint
typeRepXFingerprint (SomeTypeRep t) = typeRepFingerprint t

----------------- Showing TypeReps --------------------

-- This follows roughly the precedence structure described in Note [Precedence
-- in types].
instance Show (TypeRep (a :: k)) where
    showsPrec = showTypeable

pprFpr :: TypeRep a -> ShowS
pprFpr _ = id
--pprFpr rep = showString " (" . shows (typeRepFingerprint rep) . showString ")"

showTypeable :: Int -> TypeRep (a :: k) -> ShowS
showTypeable p rep
  = showParen True $ showTypeable' 1 rep

showTypeable' :: Int -> TypeRep (a :: k) -> ShowS
showTypeable' _ rep
  | Just HRefl <- rep `eqTypeRep` (typeRep :: TypeRep Type) =
    showChar '*'
  | isListTyCon tc, [ty] <- tys =
    showChar '[' . shows ty . showChar ']'
  | isTupleTyCon tc =
    showChar '(' . showArgs (showChar ',') tys . showChar ')'
  where (tc, tys) = splitApps rep
showTypeable' p (TrTyCon _ tycon _) =
    showParen (p > 9) $
    showsPrec p tycon
showTypeable' p (TrFun _ x r)
  = showParen (p > 8) $
    showsPrec 9 x . showString " -> " . showsPrec 8 r
showTypeable' p (TrApp _ f x)
  | otherwise =
    showParen (p > 9) $
    showsPrec 8 f .
    showChar ' ' .
    showsPrec 9 x

-- | @since 4.10.0.0
instance Show SomeTypeRep where
  showsPrec p (SomeTypeRep ty) = showsPrec p ty

splitApps :: TypeRep a -> (TyCon, [SomeTypeRep])
splitApps = undefined --go []
    {-
  where
    go :: [SomeTypeRep] -> TypeRep a -> (TyCon, [SomeTypeRep])
    go xs (TrTyCon _ tc _) = (tc, xs)
    go xs (TrApp _ f x)    = go (SomeTypeRep x : xs) f
    go _  (TrFun _ _ _)    = error "splitApps: FunTy" -- TODO
-}

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
rnfTypeRep (TrFun _ x y)     = rnfTypeRep x `seq` rnfTypeRep y

-- | Helper to fully evaluate 'SomeTypeRep' for use as @NFData(rnf)@ implementation
--
-- @since 4.10.0.0
rnfSomeTypeRep :: SomeTypeRep -> ()
rnfSomeTypeRep (SomeTypeRep r) = rnfTypeRep r

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
         -> Int#        -- ^ number of kind variables
         -> KindRep     -- ^ kind representation
         -> TyCon       -- ^ A unique 'TyCon' object
mkTyCon# pkg modl name n_kinds kind_rep
  | Fingerprint (W64# hi) (W64# lo) <- fingerprint
  = TyCon hi lo (Module (TrNameS pkg) (TrNameS modl)) (TrNameS name) n_kinds kind_rep
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
        -> Int         -- ^ number of kind variables
        -> KindRep     -- ^ kind representation
        -> TyCon        -- ^ A unique 'TyCon' object
-- Used when the strings are dynamically allocated,
-- eg from binary deserialisation
mkTyCon pkg modl name (I# n_kinds) kind_rep
  | Fingerprint (W64# hi) (W64# lo) <- fingerprint
  = TyCon hi lo (Module (TrNameD pkg) (TrNameD modl)) (TrNameD name) n_kinds kind_rep
  where
    fingerprint :: Fingerprint
    fingerprint = fingerprintString (pkg ++ (' ':modl) ++ (' ':name))

mkTypeLitTyCon :: String -> TyCon -> TyCon
mkTypeLitTyCon name kind_tycon
  = mkTyCon "base" "GHC.TypeLits" name 0 kind
  where kind = KindRepTyConApp kind_tycon []

-- | Used to make `'Typeable' instance for things of kind Nat
typeNatTypeRep :: KnownNat a => Proxy# a -> TypeRep a
typeNatTypeRep p = typeLitTypeRep (show (natVal' p)) tcNat
  where tcNat = typeRepTyCon (typeRep @Nat)

-- | Used to make `'Typeable' instance for things of kind Symbol
typeSymbolTypeRep :: KnownSymbol a => Proxy# a -> TypeRep a
typeSymbolTypeRep p = typeLitTypeRep (show (symbolVal' p)) tcSymbol
  where tcSymbol = typeRepTyCon (typeRep @Symbol)

-- | An internal function, to make representations for type literals.
typeLitTypeRep :: forall (a :: k). (Typeable k) => String -> TyCon -> TypeRep a
typeLitTypeRep nm kind_tycon = mkTrCon (mkTypeLitTyCon nm kind_tycon) []

-- | For compiler use.
mkTrFun :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep) (a :: TYPE r1) (b :: TYPE r2).
           TypeRep a -> TypeRep b -> TypeRep ((a -> b) :: Type)
mkTrFun arg res = TrFun fpr arg res
  where fpr = fingerprintFingerprints [typeRepFingerprint arg, typeRepFingerprint res]
