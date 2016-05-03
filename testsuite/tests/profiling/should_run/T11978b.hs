
import Control.Concurrent
import Control.Concurrent.MVar
import Control.Exception
import Control.Monad

main :: IO ()
main = do
    putStrLn "Start ..."
    mvar <- newMVar (0 :: Int)

    let count = 50

    forM_ [ 1 .. count ] $ const $ forkIO $ do
            threadDelay 100
            i <- takeMVar mvar
            putMVar mvar $! i + 1

    threadDelay 1000000
    end <- takeMVar mvar
    putStrLn $ "Final result " ++ show end
    assert (end == count) $ return ()
