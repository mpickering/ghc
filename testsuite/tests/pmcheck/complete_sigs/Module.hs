module Module where

import ModuleA

foo :: A -> Bool
foo B = True


data D = D | E

{-# COMPLETE D #-}

foo2 :: D -> Bool
foo2 D = False
