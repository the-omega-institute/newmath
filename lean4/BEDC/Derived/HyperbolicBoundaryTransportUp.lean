import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HyperbolicBoundaryTransportUp : Type where
  | mk
      (diskMap boundaryFarEnd reversibleTransport provenance transport replay
        metricNoncollapse localCert : BHist) :
      HyperbolicBoundaryTransportUp
  deriving DecidableEq

end BEDC.Derived
