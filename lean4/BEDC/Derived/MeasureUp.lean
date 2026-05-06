import BEDC.FKernel.Hist

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Hist

def MeasureZeroBHistCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def MeasureZeroBHistClassifier (h k : BHist) : Prop :=
  MeasureZeroBHistCarrier h ∧ MeasureZeroBHistCarrier k ∧ hsame h k

theorem MeasureZeroBHist_carrier_classifier_stability
    {h k event endpoint endpoint' : BHist} :
    MeasureZeroBHistCarrier h ->
      MeasureZeroBHistClassifier h k ->
        MeasureZeroBHistClassifier event BHist.Empty ->
          hsame endpoint BHist.Empty ->
            hsame endpoint endpoint' ->
              MeasureZeroBHistCarrier k ∧
                MeasureZeroBHistClassifier event BHist.Empty ∧
                  MeasureZeroBHistClassifier endpoint endpoint' := by
  intro hCarrier classified eventClassified endpointZero sameEndpoint
  have kCarrier : MeasureZeroBHistCarrier k :=
    hsame_trans (hsame_symm classified.right.right) hCarrier
  have endpoint'Zero : MeasureZeroBHistCarrier endpoint' :=
    hsame_trans (hsame_symm sameEndpoint) endpointZero
  have endpointClassified : MeasureZeroBHistClassifier endpoint endpoint' :=
    And.intro endpointZero (And.intro endpoint'Zero sameEndpoint)
  exact And.intro kCarrier (And.intro eventClassified endpointClassified)

theorem MeasureZeroBHist_event_row_coverage {event union value sum : BHist} :
    MeasureZeroBHistClassifier event BHist.Empty ->
      hsame value BHist.Empty ->
        hsame sum BHist.Empty ->
          hsame union BHist.Empty ->
            MeasureZeroBHistClassifier event BHist.Empty ∧
              MeasureZeroBHistClassifier union BHist.Empty ∧
                MeasureZeroBHistClassifier value sum := by
  intro eventClassified valueZero sumZero unionZero
  have unionClassified : MeasureZeroBHistClassifier union BHist.Empty :=
    And.intro unionZero (And.intro (hsame_refl BHist.Empty) unionZero)
  have valueSumSame : hsame value sum :=
    hsame_trans valueZero (hsame_symm sumZero)
  have valueSumClassified : MeasureZeroBHistClassifier value sum :=
    And.intro valueZero (And.intro sumZero valueSumSame)
  exact And.intro eventClassified (And.intro unionClassified valueSumClassified)

end BEDC.Derived.MeasureUp
