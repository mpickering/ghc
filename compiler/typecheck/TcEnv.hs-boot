module TcEnv where

import TcRnTypes( TcM )
import VarEnv( TidyEnv )
import GHC.Core.TyCo.Rep (Type)
import Var (EvVar)

-- Annoyingly, there's a recursion between tcInitTidyEnv
-- (which does zonking and hence needs TcMType) and
-- addErrTc etc which live in TcRnMonad.  Rats.
tcInitTidyEnv :: TcM TidyEnv
emitTypeable :: Type -> TcM EvVar

