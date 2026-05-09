import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SOneHistoryCarrier_equation_transport_obligation_surface
    {x y equation equation' point point' : BHist} :
    SOneHistoryCarrier x y equation point -> hsame equation equation' ->
      hsame point point' ->
        SOneHistoryCarrier x y equation' point' ∧ hsame equation' SOneUnitHistory ∧
          SOneProductHistoryCarrier point' ∧ Cont x y point' := by
  intro carrier sameEquation samePoint
  have transported : SOneHistoryCarrier x y equation' point' :=
    SOneHistoryCarrier_coordinate_transport carrier (hsame_refl x) (hsame_refl y)
      sameEquation samePoint
  exact And.intro transported
    (And.intro (SOneHistoryCarrier_equation_unit transported)
      (And.intro (SOneHistoryCarrier_real_pair transported)
        transported.right.right.right))

end BEDC.Derived.S1Up
