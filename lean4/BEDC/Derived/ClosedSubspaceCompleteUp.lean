import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ClosedSubspaceCompleteUp : Type where
  | mk
      (ambientCompleteMetric closedSet metric streamName regSeqRat cauchyName limitRetention
        transport replay provenance localName : BHist) :
      ClosedSubspaceCompleteUp
  deriving DecidableEq

end BEDC.Derived
