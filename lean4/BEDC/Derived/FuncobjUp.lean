import BEDC.Derived.ContinuousMapUp
import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.FuncobjUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ContinuousMapUp
open BEDC.Derived.LinearMapUp

theorem FuncObjLinearSingleton_continuous_map_components_empty
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      LinearMapSingletonCarrier source -> LinearMapSingletonCarrier map ->
        LinearMapSingletonCarrier modulus ->
          hsame target BHist.Empty ∧ hsame cert BHist.Empty ∧
            hsame distance BHist.Empty := by
  intro carrier sourceEmpty mapEmpty modulusEmpty
  have graphRel : Cont source map target :=
    carrier.left.right.right.right.right.left
  have certRel : Cont target modulus cert :=
    carrier.left.right.right.right.right.right
  have distanceRel : Cont source target distance :=
    carrier.right.right.right.right
  have targetEmpty : hsame target BHist.Empty :=
    cont_respects_hsame sourceEmpty mapEmpty graphRel (cont_right_unit BHist.Empty)
  have certEmpty : hsame cert BHist.Empty :=
    cont_respects_hsame targetEmpty modulusEmpty certRel (cont_right_unit BHist.Empty)
  have distanceEmpty : hsame distance BHist.Empty :=
    cont_respects_hsame sourceEmpty targetEmpty distanceRel (cont_right_unit BHist.Empty)
  exact And.intro targetEmpty (And.intro certEmpty distanceEmpty)

end BEDC.Derived.FuncobjUp
