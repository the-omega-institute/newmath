import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem SOneHistoryCarrier_shared_point_component_iff {x x' y y' e e' p : BHist} :
    SOneHistoryCarrier x y e p -> SOneHistoryCarrier x' y' e' p ->
      Cont x y p ∧ Cont x' y' p ∧
        ((hsame x x' -> hsame y y' ∧ hsame e e') ∧
          (hsame y y' -> hsame x x' ∧ hsame e e')) := by
  intro left right
  constructor
  · exact left.right.right.right
  · constructor
    · exact right.right.right.right
    · constructor
      · intro sameX
        exact SOneHistoryCarrier_coordinate_pair_right_deterministic left right sameX
      · intro sameY
        exact SOneHistoryCarrier_coordinate_pair_deterministic left right sameY

end BEDC.Derived.S1Up
