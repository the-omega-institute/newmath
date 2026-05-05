import BEDC.FKernel.Cont.Units
import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingleton_identity_tower_continuation_classified {h middle top : BHist} :
    FieldSingletonCarrier h -> Cont h BHist.Empty middle -> Cont middle BHist.Empty top ->
      FieldSingletonClassifier top h ∧ hsame middle top := by
  intro carrierH first second
  have sameMiddleH : hsame middle h := cont_right_unit_result first
  have sameTopMiddle : hsame top middle := cont_right_unit_result second
  have carrierMiddle : FieldSingletonCarrier middle := hsame_trans sameMiddleH carrierH
  have carrierTop : FieldSingletonCarrier top := hsame_trans sameTopMiddle carrierMiddle
  have sameTopH : hsame top h := hsame_trans sameTopMiddle sameMiddleH
  exact And.intro
    (And.intro carrierTop (And.intro carrierH sameTopH))
    (hsame_symm sameTopMiddle)

theorem FieldExtSingleton_scalar_action_mul_endpoint_classified {r m : BHist} :
    FieldSingletonCarrier r -> FieldSingletonCarrier m ->
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) (FieldSingletonMul r m) ∧
        FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty := by
  intro _carrierR _carrierM
  have emptyCarrier : hsame BHist.Empty BHist.Empty := hsame_refl BHist.Empty
  exact And.intro
    (And.intro emptyCarrier (And.intro emptyCarrier emptyCarrier))
    (And.intro emptyCarrier (And.intro emptyCarrier emptyCarrier))

end BEDC.Derived.FieldExtUp
