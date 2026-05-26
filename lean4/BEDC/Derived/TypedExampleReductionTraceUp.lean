import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TypedExampleReductionTraceUp : Type where
  | mk : (term type reduction checker closedness transport replay provenance name : BHist) →
      TypedExampleReductionTraceUp
  deriving DecidableEq

end BEDC.Derived
