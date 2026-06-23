import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteCauchyCompletenessCriterionUp : Type where
  | mk
      (window readback tolerance criterion bolzanoCauchyBranch realSeal transport replay
        provenance localNameCert : BHist) :
      FiniteCauchyCompletenessCriterionUp
  deriving DecidableEq

end BEDC.Derived
