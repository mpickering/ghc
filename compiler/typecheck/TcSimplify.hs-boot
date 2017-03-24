module TcSimplify where
import TcRnTypes  ( TcM )
import TcType ( TcSigmaType )

-- This boot file exists to make tcCanFitHole avaialble in TcErrors

tcCanFitHole :: TcSigmaType -> TcSigmaType -> TcM Bool
