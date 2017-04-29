module LookupSub where
import qualified LookupSubA
import qualified LookupSubB

data FD = FD

getEcho = undefined

instance LookupSubA.IODevice FD where
  getEcho = getEcho


