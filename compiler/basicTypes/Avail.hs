{-# LANGUAGE CPP #-}
--
-- (c) The University of Glasgow
--

#include "HsVersions.h"

module Avail (
    Avails,
    AvailInfo(..),
    IsExported(..),
    combIsExported,
    avail,
    availsToNameSet,
    availsToNameSetWithSelectors,
    availsToNameEnv,
    availName, availNames, availNonFldNames,
    availNamesWithSelectors,
    availFlds,
    stableAvailCmp,
    plusAvail,
    trimAvail,
    filterAvail,
    filterAvails,
    nubAvails


  ) where

import Name
import NameEnv
import NameSet

import FieldLabel
import Binary
import ListSetOps
import Outputable
import Util

import Data.List ( find )
--import Data.Function

-- -----------------------------------------------------------------------------
-- The AvailInfo type

-- | Records what things are "available", i.e. in scope
data AvailInfo = Avail Name      -- ^ An ordinary identifier in scope
               | AvailTC Name
                         IsExported
                         NameSet
                         [FieldLabel]
                                 -- ^ A type or class in scope. Parameters:
                                 --
                                 --  1) The name of the type or class
                                 --  2) The available pieces of type or class,
                                 --     excluding field selectors.
                                 --  3) The record fields of the type
                                 --     (see Note [Representing fields in AvailInfo]).
                                 --
                                 -- The AvailTC Invariant:
                                 --   * If the type or class is itself
                                 --     to be in scope, it must be
                                 --     *first* in this list.  Thus,
                                 --     typically: @AvailTC Eq [Eq, ==, \/=]@
                deriving( Eq )
                        -- Equality used when deciding if the
                        -- interface has changed

data IsExported = IsExported | NotExported deriving Eq

-- | A collection of 'AvailInfo' - several things that are \"available\"
type Avails = [AvailInfo]

{-
Note [Representing fields in AvailInfo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When -XDuplicateRecordFields is disabled (the normal case), a
datatype like

  data T = MkT { foo :: Int }

gives rise to the AvailInfo

  AvailTC T [T, MkT] [FieldLabel "foo" False foo],

whereas if -XDuplicateRecordFields is enabled it gives

  AvailTC T [T, MkT] [FieldLabel "foo" True $sel:foo:MkT]

since the label does not match the selector name.

The labels in a field list are not necessarily unique:
data families allow the same parent (the family tycon) to have
multiple distinct fields with the same label. For example,

  data family F a
  data instance F Int  = MkFInt { foo :: Int }
  data instance F Bool = MkFBool { foo :: Bool}

gives rise to

  AvailTC F [F, MkFInt, MkFBool]
    [FieldLabel "foo" True $sel:foo:MkFInt, FieldLabel "foo" True $sel:foo:MkFBool].

Moreover, note that the flIsOverloaded flag need not be the same for
all the elements of the list.  In the example above, this occurs if
the two data instances are defined in different modules, one with
`-XDuplicateRecordFields` enabled and one with it disabled.  Thus it
is possible to have

  AvailTC F [F, MkFInt, MkFBool]
    [FieldLabel "foo" True $sel:foo:MkFInt, FieldLabel "foo" False foo].

If the two data instances are defined in different modules, both
without `-XDuplicateRecordFields`, it will be impossible to export
them from the same module (even with `-XDuplicateRecordfields`
enabled), because they would be represented identically.  The
workaround here is to enable `-XDuplicateRecordFields` on the defining
modules.
-}

-- | Compare lexicographically
stableAvailCmp :: AvailInfo -> AvailInfo -> Ordering
stableAvailCmp (Avail n1)       (Avail n2)   = n1 `stableNameCmp` n2
stableAvailCmp (Avail {})         (AvailTC {})   = LT
stableAvailCmp (AvailTC n _ _ns _nfs) (AvailTC m _ _ms _mfs) =
    (n `stableNameCmp` m)
stableAvailCmp (AvailTC {})       (Avail {})     = GT

avail :: Name -> AvailInfo
avail n = Avail n

-- -----------------------------------------------------------------------------
-- Operations on AvailInfo

availsToNameSet :: [AvailInfo] -> NameSet
availsToNameSet avails = foldr add emptyNameSet avails
      where add avail set = extendNameSetList set (availNames avail)

availsToNameSetWithSelectors :: [AvailInfo] -> NameSet
availsToNameSetWithSelectors avails = foldr add emptyNameSet avails
      where add avail set = extendNameSetList set (availNamesWithSelectors avail)

availsToNameEnv :: [AvailInfo] -> NameEnv AvailInfo
availsToNameEnv avails = foldr add emptyNameEnv avails
     where add avail env = extendNameEnvList env
                                (zip (availNames avail) (repeat avail))

-- | Just the main name made available, i.e. not the available pieces
-- of type or class brought into scope by the 'GenAvailInfo'
availName :: AvailInfo -> Name
availName (Avail n)     = n
availName (AvailTC n _ _ _) = n

-- | All names made available by the availability information (excluding overloaded selectors)
availNames :: AvailInfo -> [Name]
availNames (Avail n)         = [n]
availNames (AvailTC _ _ ns fs) = nameSetElemsStable ns ++ [ flSelector f | f <- fs, not (flIsOverloaded f) ]

-- | All names made available by the availability information (including overloaded selectors)
availNamesWithSelectors :: AvailInfo -> [Name]
availNamesWithSelectors (Avail n)         = [n]
availNamesWithSelectors (AvailTC _ _ ns fs) = nameSetElemsStable ns ++ map flSelector fs

-- | Names for non-fields made available by the availability information
availNonFldNames :: AvailInfo -> [Name]
availNonFldNames (Avail n)        = [n]
availNonFldNames (AvailTC _ _ ns _) = nameSetElemsStable ns

-- | Fields made available by the availability information
availFlds :: AvailInfo -> [FieldLabel]
availFlds (AvailTC _ _ _ fs) = fs
availFlds _                = []


-- -----------------------------------------------------------------------------
-- Utility

combIsExported :: IsExported -> IsExported -> IsExported
combIsExported IsExported _ = IsExported
combIsExported _ IsExported = IsExported
combIsExported NotExported NotExported = NotExported

plusAvail :: AvailInfo -> AvailInfo -> AvailInfo
plusAvail a1 a2
  | debugIsOn && availName a1 /= availName a2
  = pprPanic "RnEnv.plusAvail names differ" (hsep [ppr a1,ppr a2])
plusAvail a1@(Avail {})         (Avail {})        = a1
plusAvail (AvailTC n1 ic ss1 fs1) (AvailTC _n2 ic' ss2 fs2)
  = AvailTC n1 (combIsExported ic ic')
               (plusNameEnv ss1 ss2)
               (fs1 `unionLists` fs2)
plusAvail a1 a2 = pprPanic "RnEnv.plusAvail" (hsep [ppr a1,ppr a2])

-- | trims an 'AvailInfo' to keep only a single name
trimAvail :: AvailInfo -> Name -> AvailInfo
trimAvail (Avail n)         _ = Avail n
trimAvail (AvailTC n _ic ns fs) m = case find ((== m) . flSelector) fs of
    Just x  -> AvailTC n NotExported emptyNameSet [x]
    Nothing -> ASSERT( m `elemNameSet` ns ) AvailTC n NotExported (unitNameSet m) []

-- | filters 'AvailInfo's by the given predicate
filterAvails  :: (Name -> Bool) -> [AvailInfo] -> [AvailInfo]
filterAvails keep avails = foldr (filterAvail keep) [] avails

-- | filters an 'AvailInfo' by the given predicate
filterAvail :: (Name -> Bool) -> AvailInfo -> [AvailInfo] -> [AvailInfo]
filterAvail keep ie rest =
  case ie of
    Avail n | keep n    -> ie : rest
            | otherwise -> rest
    AvailTC tc _ic ns fs ->
        let ns' = filterNameSet keep ns
            fs' = filter (keep . flSelector) fs in
        if isEmptyNameSet ns' && null fs' then rest else AvailTC tc NotExported ns' fs' : rest


-- | Combines 'AvailInfo's from the same family
-- 'avails' may have several items with the same availName
-- E.g  import Ix( Ix(..), index )
-- will give Ix(Ix,index,range) and Ix(index)
-- We want to combine these; addAvail does that
nubAvails :: [AvailInfo] -> [AvailInfo]
nubAvails avails = nameEnvElts (foldl add emptyNameEnv avails)
  where
    add env avail = extendNameEnv_C plusAvail env (availName avail) avail

-- -----------------------------------------------------------------------------
-- Printing

instance Outputable AvailInfo where
   ppr = pprAvail

pprAvail :: AvailInfo -> SDoc
pprAvail (Avail n)
  = ppr n
pprAvail (AvailTC n _ic ns fs)
  = ppr n <> braces (sep [ (ppr ns) <> semi
                         , fsep (punctuate comma (map (ppr . flLabel) fs))])

instance Binary AvailInfo where
    put_ bh (Avail aa) = do
            putByte bh 0
            put_ bh aa
    put_ bh (AvailTC ab ic ac ad) = do
            putByte bh 1
            put_ bh ab
            put_ bh ic
            put_ bh (nameSetElemsStable ac)
            put_ bh ad
    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      return (Avail aa)
              _ -> do ab <- get bh
                      ic <- get bh
                      ac <- mkNameSet <$> get bh
                      ad <- get bh
                      return (AvailTC ic ab ac ad)

instance Binary IsExported where
  put_ bh IsExported = putByte bh 0
  put_ bh NotExported = putByte bh 1

  get bh = do
    h <- getByte bh
    case h of
      0 -> return IsExported
      _ -> return NotExported
