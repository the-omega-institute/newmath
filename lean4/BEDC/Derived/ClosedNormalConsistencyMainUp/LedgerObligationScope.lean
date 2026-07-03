import BEDC.Derived.ClosedNormalConsistencyMainUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedNormalConsistencyMainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedNormalConsistencyMainLedgerObligationScope
    {T L B _F R H C P N endpointRead contradictionRead structuralRead : BHist} :
    Cont T L endpointRead →
      Cont endpointRead B contradictionRead →
        Cont contradictionRead C structuralRead →
          hsame structuralRead (append (append (append T L) B) C) ∧
            hsame R R ∧ hsame H H ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro endpointRoute contradictionRoute structuralRoute
  cases endpointRoute
  cases contradictionRoute
  cases structuralRoute
  exact
    ⟨hsame_refl (append (append (append T L) B) C), hsame_refl R, hsame_refl H,
      hsame_refl P, hsame_refl N⟩

end BEDC.Derived.ClosedNormalConsistencyMainUp
