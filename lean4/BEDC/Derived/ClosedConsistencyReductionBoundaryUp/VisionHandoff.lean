import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedConsistencyReductionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedConsistencyReductionBoundaryCarrier_vision_handoff
    {S Q E D K O H read frontierRead : BHist} :
    Cont S Q E →
      Cont E D K →
        Cont K O read →
          Cont read H frontierRead →
            hsame frontierRead (append S (append Q (append D (append O H)))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro sourceRoute dischargeRoute obstructionRoute frontierRoute
  cases sourceRoute
  cases dischargeRoute
  cases obstructionRoute
  cases frontierRoute
  exact
    (append_assoc (append (append S Q) D) O H).trans
      ((append_assoc (append S Q) D (append O H)).trans
        (append_assoc S Q (append D (append O H))))

end BEDC.Derived.ClosedConsistencyReductionBoundaryUp
