import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem SOneHistoryCarrier_product_real_ledger_obligation_surface
    {x y equation point x' y' equation' point' : BHist} :
    SOneHistoryCarrier x y equation point -> hsame x x' -> hsame y y' ->
      hsame equation equation' -> hsame point point' ->
        (SOneProductHistoryCarrier point ∧ hsame equation SOneUnitHistory ∧
          ∃ dx dy : BHist,
            hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
              hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x y point) ∧
          (SOneProductHistoryCarrier point' ∧ hsame equation' SOneUnitHistory ∧
            ∃ dx dy : BHist,
              hsame x' (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
                hsame y' (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x' y' point') := by
  intro carrier sameX sameY sameEquation samePoint
  exact And.intro (SOneHistoryCarrier_public_readback carrier)
    (SOneHistoryCarrier_public_readback_transport carrier sameX sameY sameEquation samePoint)

end BEDC.Derived.S1Up
