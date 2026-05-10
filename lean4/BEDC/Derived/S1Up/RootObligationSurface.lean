import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RealUp

theorem SOneHistoryCarrier_root_obligation_surface {x y equation point : BHist} :
    SOneHistoryCarrier x y equation point ->
      RealConstantHistoryCarrier x ∧ RealConstantHistoryCarrier y ∧
        SOneProductHistoryCarrier point ∧
          RealConstantHistoryClassifier equation SOneUnitHistory ∧ Cont x y point ∧
            hsame equation SOneUnitHistory := by
  intro carrier
  have productCarrier : SOneProductHistoryCarrier point :=
    SOneHistoryCarrier_real_pair carrier
  have equationSame : hsame equation SOneUnitHistory :=
    SOneHistoryCarrier_equation_unit carrier
  exact ⟨carrier.left, carrier.right.left, productCarrier, carrier.right.right.left,
    carrier.right.right.right, equationSame⟩

end BEDC.Derived.S1Up
