import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FinitePhaseCylinderUp : Type where
  | mk
      (complexPhase boundaryCircle diskMetric unitaryTransport phaseWindow refusalLedger
        transport replay provenance name : BHist) :
      FinitePhaseCylinderUp
  deriving DecidableEq

end BEDC.Derived
