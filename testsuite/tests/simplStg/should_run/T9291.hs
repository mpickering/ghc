{-# LANGUAGE MagicHash #-}
import GHC.Exts
import Unsafe.Coerce

foo :: Either Int a -> Either Bool a
foo (Left 0) = Left True
foo (Left _) = Left False
foo (Right x) = Right x
{-# NOINLINE foo #-}

bar :: a -> (Either Int a, Either Bool a)
bar x = (Right x, Right x)
{-# NOINLINE bar #-}

test x = do
    let (r1,r2) = bar x
    (same $! r1) $! r2
    let r3 = foo r1
    (same $! r1) $!  r3
{-# NOINLINE test #-}

main = test "foo"

same :: a -> b -> IO ()
same x y = case reallyUnsafePtrEquality# (unsafeCoerce x) y of
    1# -> putStrLn "yes"
    _  -> putStrLn "no"
