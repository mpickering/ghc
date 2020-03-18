module TcRnTypes where
import Prelude(Int)
import TcType
import SrcLoc

data TcLclEnv
data ThStage
type ThLevel = Int

thLevel :: ThStage -> Int

setLclEnvTcLevel :: TcLclEnv -> TcLevel -> TcLclEnv
getLclEnvTcLevel :: TcLclEnv -> TcLevel

getLclEnvThLevel :: TcLclEnv -> ThLevel

setLclEnvLoc :: TcLclEnv -> RealSrcSpan -> TcLclEnv
getLclEnvLoc :: TcLclEnv -> RealSrcSpan
