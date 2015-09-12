{-# LANGUAGE PatternSynonyms #-}
module Main where

pattern ReqNoProv :: () => Show a => a -> Maybe a
pattern ReqNoProv{j} = Just j

data A  = A deriving (Show)


p1 = ReqNoProv True
{-
p2 (ReqNoProv r) = r

p3 = p2 p1

p4 (ReqNoProv {j = foo}) = foo

p5 = p4 p1
-}

p7 (ReqNoProv _) = ReqNoProv False


p6 = p1 {j = False}

p8 = p1 { j = A }


main = print p6

