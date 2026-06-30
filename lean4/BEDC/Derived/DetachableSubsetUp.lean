import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DetachableSubsetUp : Type where
  | mk (carrier membership complement boolGate transport replay provenance name : BHist) :
      DetachableSubsetUp
  deriving DecidableEq

end BEDC.Derived
