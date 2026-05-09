import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem SOneHistoryCarrier_public_constructor_scope {x y e p : BHist} :
    SOneHistoryCarrier x y e p ->
      SOneProductHistoryCarrier p ∧ hsame e SOneUnitHistory ∧ Cont x y p ∧
        (exists dx dy : BHist,
          hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
            hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x y p) ∧
          (hsame p BHist.Empty -> False) := by
  intro carrier
  have readback := SOneHistoryCarrier_public_readback carrier
  constructor
  · exact readback.left
  · constructor
    · exact readback.right.left
    · constructor
      · exact carrier.right.right.right
      · constructor
        · exact readback.right.right
        · intro sameEmpty
          have emptyCarrier :
              SOneHistoryCarrier x y e BHist.Empty :=
            SOneHistoryCarrier_coordinate_transport carrier (hsame_refl x) (hsame_refl y)
              (hsame_refl e) sameEmpty
          exact SOneHistoryCarrier_empty_point_absurd emptyCarrier

end BEDC.Derived.S1Up
