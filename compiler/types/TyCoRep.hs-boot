module TyCoRep where

import Outputable ( SDoc )
import Data.Data  ( Data )

data Type
data TyThing
data Coercion
data LeftOrRight
data UnivCoProvenance
data TCvSubst
data TyLit
data TyBinder
data TyPrec

type PredType = Type
type Kind = Type
type ThetaType = [PredType]

pprKind :: Kind -> SDoc
pprType :: Type -> SDoc

instance Data Type
  -- To support Data instances in CoAxiom

