{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}
module T13154a where

import Data.Kind
import GHC.Exts

class Foo1 (a :: TYPE ('TupleRep '[]))
deriving instance Foo1 a

class Foo2 (a :: TYPE ('TupleRep '[]))
deriving instance Foo2 (##)

class Foo3 (a :: TYPE ('SumRep '[ 'LiftedRep, 'LiftedRep ]))
deriving instance Foo3 a

class Foo4 (a :: TYPE ('SumRep '[ 'LiftedRep, 'LiftedRep ]))
deriving instance Foo4 (# a | b #)

class Foo5 (a :: Type)
deriving instance Foo5 a

class C
deriving instance C
