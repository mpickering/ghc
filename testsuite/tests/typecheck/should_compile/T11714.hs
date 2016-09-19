{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UnboxedTuples #-}

module T11714 where

import Data.Proxy
import GHC.Exts

f :: Proxy ((->) Int)
f = Proxy

g :: Proxy ((->) Int#)
g = Proxy

h :: Proxy ((->) (# Int#, Char #))
h = Proxy
