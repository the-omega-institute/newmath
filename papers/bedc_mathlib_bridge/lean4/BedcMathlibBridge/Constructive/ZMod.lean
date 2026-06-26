import BEDC.Derived.ZModUp
import Mathlib.Data.ZMod.Defs

namespace BedcMathlibBridge.Constructive.ZMod

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary

def mathlibCarrier (n : BHist) : Type :=
  _root_.ZMod (bwordLength n)

def bedcCarrier (n : BHist) : Type :=
  BEDC.Derived.ZModUp.ZMod n × mathlibCarrier n

end BedcMathlibBridge.Constructive.ZMod
