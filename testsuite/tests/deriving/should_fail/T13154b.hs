{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UnboxedTuples #-}
module T13154b where

import GHC.Exts

-- Test some nonsense configurations

class Foo (a :: TYPE ('TupleRep '[]))
deriving stock   instance Foo a
deriving stock   instance Foo (##)
deriving newtype instance Foo a
deriving newtype instance Foo (##)

class C
deriving stock   instance C
deriving newtype instance C
