{-# LANGUAGE PatternSynonyms #-}
module Main where

pattern ReqNoProv :: () => Show a => a -> Maybe a
pattern ReqNoProv{j} = Just j

p1 = ReqNoProv True

p7 (ReqNoProv _) = ReqNoProv False

p6 = p1 {j = False}

main = print p6
