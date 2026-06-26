import BedcMathlibBridge.Audit.ThinLayerGuardCore
import BEDC.FKernel.Hist

namespace BedcMathlibBridge.Constructive.ThinLayerNegative

def pureBedcCarrier : BEDC.FKernel.Hist.BHist :=
  BEDC.FKernel.Hist.BHist.Empty

end BedcMathlibBridge.Constructive.ThinLayerNegative

run_cmd do
  BedcMathlibBridge.Audit.ThinLayerGuard.auditSelected #[
    `BedcMathlibBridge.Constructive.ThinLayerNegative.pureBedcCarrier
  ]
