import BEDC.Derived.ClosedConsistencyReductionBoundaryUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedConsistencyReductionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedConsistencyReductionBoundaryCarrier_obstruction_readback
    {S Q E D K O read : BHist}
    (sourceRoute : Cont S Q E)
    (dischargeRoute : Cont E D K)
    (obstructionRoute : Cont K O read) :
    hsame read (append S (append Q (append D O))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases sourceRoute
  cases dischargeRoute
  cases obstructionRoute
  exact (append_assoc (append S Q) D O).trans (append_assoc S Q (append D O))

end BEDC.Derived.ClosedConsistencyReductionBoundaryUp
