import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LipschitzSpaceUp : Type where
  | mk
      (metricDomain realMap rationalConstant inequalityLedger transport replay provenance name :
        BHist) :
      LipschitzSpaceUp
  deriving DecidableEq

end BEDC.Derived
