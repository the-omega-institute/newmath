import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier

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

theorem field_rat_carrier_non_singleton_boundary_witness :
    BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
      (FieldSingletonCarrier (BHist.e1 BHist.Empty) -> False) ∧
        ((forall h : BHist, BEDC.Derived.RatUp.RatHistoryCarrier h ->
          FieldSingletonCarrier h) -> False) := by
  have ratBoundary : BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    BEDC.Derived.RatUp.RatHistoryCarrier_e1_tail_unary_iff.mpr
      BEDC.FKernel.Unary.unary_empty
  have singletonAbsurd : FieldSingletonCarrier (BHist.e1 BHist.Empty) -> False := by
    intro singleton
    exact BEDC.Derived.RatUp.RatHistoryCarrier_not_empty ratBoundary singleton
  constructor
  · exact ratBoundary
  · constructor
    · exact singletonAbsurd
    · intro carrierCoverage
      exact singletonAbsurd (carrierCoverage (BHist.e1 BHist.Empty) ratBoundary)

theorem field_rat_carrier_singleton_coverage_obstruction :
    BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
      (fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False) ∧
      ((∀ h : BHist, BEDC.Derived.RatUp.RatHistoryCarrier h -> fieldSingletonEmptyCarrier h) ->
        False) := by
  have carrierD1 : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have notSingleton : fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False := by
    intro singletonD1
    exact RatHistoryCarrier_not_empty carrierD1 singletonD1
  constructor
  · exact carrierD1
  · constructor
    · exact notSingleton
    · intro coverage
      exact notSingleton (coverage (BHist.e1 BHist.Empty) carrierD1)

end BEDC.Derived.FieldUp
