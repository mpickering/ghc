module ConLike where
import Data.Typeable
import Name (NamedThing)
import {-# SOURCE #-} DataCon (DataCon)
import {-# SOURCE #-} PatSyn (PatSyn)
import Outputable
import Data.Data (Data)

data ConLike = RealDataCon DataCon
             | PatSynCon PatSyn
  deriving Data.Typeable.Typeable

instance Eq ConLike
instance Ord ConLike
instance NamedThing ConLike
instance Data ConLike
instance Outputable ConLike
instance OutputableBndr ConLike
