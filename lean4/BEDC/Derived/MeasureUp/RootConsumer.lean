import BEDC.Derived.MeasureUp

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MeasureIntegralConsumer_rows
    {event diff union valueEvent valueDiff valueUnion valueSum endpoint total : BHist} :
    MeasureZeroBHistClassifier event BHist.Empty ->
      MeasureZeroBHistClassifier diff BHist.Empty ->
        Cont event diff union ->
          hsame valueEvent event ->
            hsame valueDiff diff ->
              hsame valueUnion union ->
                Cont valueEvent valueDiff valueSum ->
                  Cont union BHist.Empty endpoint ->
                    Cont endpoint BHist.Empty total ->
                      MeasureZeroBHistClassifier valueSum valueUnion ∧
                        MeasureZeroBHistClassifier endpoint BHist.Empty ∧
                          MeasureZeroBHistCarrier total ∧ UnaryHistory total := by
  intro eventClassified diffClassified unionRow sameValueEvent sameValueDiff sameValueUnion
    valueRow endpointRow totalRow
  have valueClassified : MeasureZeroBHistClassifier valueSum valueUnion :=
    MeasureFiniteDisjointUnion_additivity eventClassified diffClassified unionRow sameValueEvent
      sameValueDiff sameValueUnion valueRow
  have unionZero : MeasureZeroBHistCarrier union :=
    cont_respects_hsame eventClassified.left diffClassified.left unionRow
      (cont_left_unit BHist.Empty)
  have endpointUnion : hsame endpoint union :=
    cont_right_unit_result endpointRow
  have endpointZero : MeasureZeroBHistCarrier endpoint :=
    hsame_trans endpointUnion unionZero
  have endpointClassified : MeasureZeroBHistClassifier endpoint BHist.Empty :=
    And.intro endpointZero (And.intro (hsame_refl BHist.Empty) endpointZero)
  have totalEndpoint : hsame total endpoint :=
    cont_right_unit_result totalRow
  have totalZero : MeasureZeroBHistCarrier total :=
    hsame_trans totalEndpoint endpointZero
  have totalUnary : UnaryHistory total :=
    unary_transport unary_empty (hsame_symm totalZero)
  exact And.intro valueClassified
    (And.intro endpointClassified (And.intro totalZero totalUnary))

end BEDC.Derived.MeasureUp
