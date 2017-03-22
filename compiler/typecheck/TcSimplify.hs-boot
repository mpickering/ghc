module TcSimplify where
import TcRnTypes  ( TcM )
import Type ( Type )

-- This boot file exists to make tcCanSubsume avaialble
-- when finding valid substitutions for holes

tcCanSubsume :: Type -> Type -> TcM Bool
