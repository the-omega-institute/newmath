import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DarbouxOscillationCriterionUp : Type where
  | mk
      (integral sum lower upper oscillation partition regular realSeal
        transport replay provenance name : BHist) :
      DarbouxOscillationCriterionUp
  deriving DecidableEq

end BEDC.Derived
