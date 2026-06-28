import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TailDiameterCriterionUp : Type where
  | mk
      (source tolerance tailBound criterion comparison handoff transport replay provenance
        localName : BHist) :
      TailDiameterCriterionUp
  deriving DecidableEq

end BEDC.Derived
