import BEDC.Derived.MeasureUp
import BEDC.Derived.MeasureUp.RootPublicObligationBasis

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem MeasureRootCarrierClassifier_public_obligation
    {h k event endpoint endpoint' diff diff' union union' : BHist} :
    MeasureZeroBHistCarrier h -> MeasureZeroBHistClassifier h k ->
      MeasureZeroBHistClassifier event BHist.Empty ->
        MeasureZeroBHistClassifier diff BHist.Empty ->
          hsame event endpoint -> hsame event endpoint' -> hsame diff diff' ->
            Cont event diff union -> Cont endpoint' diff' union' ->
              MeasureZeroBHistCarrier k ∧ MeasureZeroBHistCarrier diff' ∧
                MeasureZeroBHistClassifier union union' ∧
                  MeasureZeroBHistClassifier endpoint endpoint' := by
  intro hCarrier classified eventClassified diffClassified sameEventEndpoint
    sameEventEndpoint' sameDiff unionRow unionRow'
  have endpointZero : MeasureZeroBHistCarrier endpoint :=
    hsame_trans (hsame_symm sameEventEndpoint) eventClassified.left
  have sameEndpoint : hsame endpoint endpoint' :=
    hsame_trans (hsame_symm sameEventEndpoint) sameEventEndpoint'
  have stableRows :=
    MeasureZeroBHist_carrier_classifier_stability hCarrier classified eventClassified endpointZero
      sameEndpoint
  have diff'Carrier : MeasureZeroBHistCarrier diff' :=
    hsame_trans (hsame_symm sameDiff) diffClassified.left
  have unionSame : hsame union union' :=
    cont_respects_hsame sameEventEndpoint' sameDiff unionRow unionRow'
  have unionCarrier : MeasureZeroBHistCarrier union :=
    cont_respects_hsame eventClassified.left diffClassified.left unionRow
      (cont_left_unit BHist.Empty)
  have union'Carrier : MeasureZeroBHistCarrier union' :=
    hsame_trans (hsame_symm unionSame) unionCarrier
  have unionClassified : MeasureZeroBHistClassifier union union' :=
    And.intro unionCarrier (And.intro union'Carrier unionSame)
  exact And.intro stableRows.left
    (And.intro diff'Carrier (And.intro unionClassified stableRows.right.right))

theorem MeasureRootSigmaAdditive_public_obligation
    {event union value sum endpoint tail total : BHist} :
    MeasureRootPublicObligationBasis event union value sum endpoint ->
      Cont endpoint BHist.Empty total ->
        Cont BHist.Empty BHist.Empty tail ->
          Cont tail BHist.Empty sum ->
            MeasureEventRowCoverage event union value sum endpoint ∧
              MeasureZeroBHistCarrier total ∧ MeasureZeroBHistCarrier tail ∧
                hsame total endpoint ∧ hsame tail BHist.Empty := by
  intro basis endpointTotal tailCont tailSum
  have publicRows :
      MeasureEventRowCoverage event union value sum endpoint ∧ hsame endpoint BHist.Empty :=
    MeasureRootPublicObligationBasis_event_row_coverage basis
  have totalEndpoint : hsame total endpoint :=
    cont_right_unit_result endpointTotal
  have totalZero : MeasureZeroBHistCarrier total :=
    hsame_trans totalEndpoint publicRows.right
  have tailRows : hsame tail BHist.Empty ∧ hsame sum BHist.Empty ∧ hsame sum tail :=
    MeasureCountableZeroTail_canonical tailCont tailSum
  exact
    And.intro publicRows.left
      (And.intro totalZero
        (And.intro tailRows.left (And.intro totalEndpoint tailRows.left)))

end BEDC.Derived.MeasureUp
