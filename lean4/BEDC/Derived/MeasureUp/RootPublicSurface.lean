import BEDC.Derived.MeasureUp

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

end BEDC.Derived.MeasureUp
