module TcSimplify where
import TcRnTypes  ( TcM )
import Type ( Type )

-- This boot file exists to make tcCanFitHole avaialble in TcErrors

tcCanFitHole :: Type -> Type -> TcM Bool
