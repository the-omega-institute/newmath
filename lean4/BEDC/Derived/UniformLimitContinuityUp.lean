import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformLimitContinuityUp : Type where
  | mk
      (family sharedModulus tailLedger regularHandoff realSeal continuousGraph
        uniformConsumer transport replay provenance localName : BHist) :
      UniformLimitContinuityUp
  deriving DecidableEq

end BEDC.Derived
