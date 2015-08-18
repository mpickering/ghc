module DataCon where
import Var( TyVar, Id )
import Name( Name, NamedThing )
import {-# SOURCE #-} TyCon( TyCon, FieldLabel )
import Unique ( Uniquable )
import Outputable ( Outputable, OutputableBndr )
import BasicTypes (Arity)
import qualified Data.Data as Data
import {-# SOURCE #-} TypeRep (Type, ThetaType)

data DataCon
data DataConRep

data HsImplBang

dataConName      :: DataCon -> Name
dataConTyCon     :: DataCon -> TyCon
dataConExTyVars  :: DataCon -> [TyVar]
dataConSourceArity  :: DataCon -> Arity
dataConFieldLabels :: DataCon -> [FieldLabel]
dataConInstOrigArgTys  :: DataCon -> [Type] -> [Type]
dataConStupidTheta :: DataCon -> ThetaType
dataConWrapId :: DataCon -> Id
dataConImplBangs :: DataCon -> [HsImplBang]

instance Eq DataCon
instance Ord DataCon
instance Uniquable DataCon
instance NamedThing DataCon
instance Outputable DataCon
instance OutputableBndr DataCon
