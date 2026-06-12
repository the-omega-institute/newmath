import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RootChoiceSeparationUp : Type where
  | mk
      (functionRead interval apartness bisectionSchedule stream regSeq realSeal transport replay
        provenance name : BHist) :
      RootChoiceSeparationUp
  deriving DecidableEq

end BEDC.Derived
