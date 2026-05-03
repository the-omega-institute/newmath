import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.EquivCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.AdjunctionUp
open BEDC.Derived.NatTransUp

theorem EquivCatAdjunction_empty_roundtrip_identity_components
    {p q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty ->
        NatTransPrefixComponentCarrier p q a BHist.Empty ∧
          NatTransPrefixComponentCarrier q p a BHist.Empty := by
  intro carrier leftEmpty rightEmpty
  have unitCounitEmpty : unit = BHist.Empty ∧ counit = BHist.Empty := by
    cases leftEmpty
    exact cont_empty_result_inversion carrier.right.right.left
  have counitUnitEmpty : counit = BHist.Empty ∧ unit = BHist.Empty := by
    cases rightEmpty
    exact cont_empty_result_inversion carrier.right.right.right
  cases unitCounitEmpty.left
  cases unitCounitEmpty.right
  cases counitUnitEmpty.left
  cases counitUnitEmpty.right
  exact And.intro carrier.left carrier.right.left

end BEDC.Derived.EquivCatUp
