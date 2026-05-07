import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.MeasureUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SpectralTheoremCarrierClassifier_obligation
    {operator spectrum projection calculus endpoint : BHist} :
    VecSpaceSingletonCarrier operator ->
      MeasureZeroBHistCarrier spectrum ->
        MeasureZeroBHistClassifier projection BHist.Empty ->
          Cont operator spectrum calculus ->
            Cont calculus projection endpoint ->
              VecSpaceSingletonClassifier operator BHist.Empty ∧
                RealConstantHistoryClassifier (HilbertSingletonInnerProduct operator BHist.Empty)
                  (BHist.e1 (BHist.e1 BHist.Empty)) ∧
                  MeasureZeroBHistClassifier spectrum BHist.Empty ∧
                    MeasureZeroBHistClassifier projection BHist.Empty ∧
                      hsame calculus BHist.Empty ∧ hsame endpoint BHist.Empty := by
  intro operatorCarrier spectrumCarrier projectionClassified calculusRow endpointRow
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have operatorClassified : VecSpaceSingletonClassifier operator BHist.Empty :=
    And.intro operatorCarrier (And.intro emptyVecCarrier operatorCarrier)
  have innerRow :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct operator BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    (HilbertSingleton_projection_carried_endpoint operatorCarrier).right.right.right.right
  have spectrumClassified : MeasureZeroBHistClassifier spectrum BHist.Empty :=
    And.intro spectrumCarrier (And.intro (hsame_refl BHist.Empty) spectrumCarrier)
  have calculusEmpty : hsame calculus BHist.Empty :=
    cont_respects_hsame operatorCarrier spectrumCarrier calculusRow (cont_left_unit BHist.Empty)
  have endpointEmpty : hsame endpoint BHist.Empty :=
    cont_respects_hsame calculusEmpty projectionClassified.left endpointRow
      (cont_left_unit BHist.Empty)
  exact And.intro operatorClassified
    (And.intro innerRow
      (And.intro spectrumClassified
        (And.intro projectionClassified (And.intro calculusEmpty endpointEmpty))))

end BEDC.Derived.SpectralTheoremUp
