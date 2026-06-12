import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ClosedObservationProofTraceUp : Type where
  | packet
      (observation termination transport replay provenance name refusal kernel trace : BHist) :
      ClosedObservationProofTraceUp
  deriving DecidableEq

end BEDC.Derived
