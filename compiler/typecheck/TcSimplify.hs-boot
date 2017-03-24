module TcSimplify where
import TcRnTypes  ( TcM )
import TcType ( TcSigmaType )

-- This boot file exists to make tcCanSubsume avaialble in TcErrors

tcSubsumes :: TcSigmaType -> TcSigmaType -> TcM Bool
