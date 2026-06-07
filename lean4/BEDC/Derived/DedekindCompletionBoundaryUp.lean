import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DedekindCompletionBoundaryUp : Type where
  | mk
      (locatedCut regularReadback dyadicLedger streamWindow realSeal transport replay
        provenance name : BHist) :
      DedekindCompletionBoundaryUp
  deriving DecidableEq

end BEDC.Derived
