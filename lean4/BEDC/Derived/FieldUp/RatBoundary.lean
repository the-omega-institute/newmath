import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_rat_history_carrier_non_singleton_boundary_witness :
    BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) /\
      (fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False) /\
      ((forall h : BHist, BEDC.Derived.RatUp.RatHistoryCarrier h ->
        fieldSingletonEmptyCarrier h) -> False) := by
  have positiveDenominator :
      BEDC.Derived.RatUp.PositiveUnaryDenominator (BHist.e1 BHist.Empty) :=
    BEDC.Derived.RatUp.PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty
  have ratCarrier :
      BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    BEDC.Derived.RatUp.RatHistoryCarrier_iff_positive_denominator.mpr positiveDenominator
  have singletonAbsurd : fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False := by
    intro singletonCarrier
    exact BEDC.Derived.RatUp.RatHistoryCarrier_not_empty ratCarrier singletonCarrier
  exact And.intro ratCarrier
    (And.intro singletonAbsurd
      (by
        intro coverage
        exact singletonAbsurd (coverage (BHist.e1 BHist.Empty) ratCarrier)))

end BEDC.Derived.FieldUp
