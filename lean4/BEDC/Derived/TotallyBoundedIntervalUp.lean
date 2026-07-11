import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TotallyBoundedIntervalUp : Type where
  | mk
      (lowerEndpoint upperEndpoint locatedMembership dyadicMeshRadius regSeqRatReadback
        meshSchedule finiteNet realSeal transport replay provenance localNameCert : BHist) :
      TotallyBoundedIntervalUp
  deriving DecidableEq

end BEDC.Derived
