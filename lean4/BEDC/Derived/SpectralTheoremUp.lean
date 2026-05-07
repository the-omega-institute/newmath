import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.Derived.MeasureUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SpectralTheoremOperatorSpectralData_carrier_classifier
    {operator operator' spectrum pvm calculus calculus' : BHist} :
    VecSpaceSingletonClassifier operator operator' ->
      MeasureZeroBHistCarrier spectrum ->
        MeasureZeroBHistCarrier pvm ->
          Cont spectrum pvm calculus ->
            hsame calculus calculus' ->
              VecSpaceSingletonCarrier operator' ∧
                MeasureZeroBHistClassifier spectrum BHist.Empty ∧
                  MeasureZeroBHistClassifier pvm BHist.Empty ∧
                    MeasureZeroBHistCarrier calculus' := by
  intro operatorClassified spectrumCarrier pvmCarrier calculusRow sameCalculus
  have emptyCarrier : MeasureZeroBHistCarrier BHist.Empty := hsame_refl BHist.Empty
  have spectrumClassified : MeasureZeroBHistClassifier spectrum BHist.Empty :=
    And.intro spectrumCarrier (And.intro emptyCarrier spectrumCarrier)
  have pvmClassified : MeasureZeroBHistClassifier pvm BHist.Empty :=
    And.intro pvmCarrier (And.intro emptyCarrier pvmCarrier)
  have calculusCarrier : MeasureZeroBHistCarrier calculus :=
    cont_respects_hsame spectrumCarrier pvmCarrier calculusRow (cont_left_unit BHist.Empty)
  have calculusTargetCarrier : MeasureZeroBHistCarrier calculus' :=
    hsame_trans (hsame_symm sameCalculus) calculusCarrier
  exact And.intro operatorClassified.right.left
    (And.intro spectrumClassified (And.intro pvmClassified calculusTargetCarrier))

def SpectralTheoremCarrier
    (endpoint operator spectrum projection calculus provenance : BHist) : Prop :=
  UnaryHistory operator ∧ UnaryHistory spectrum ∧ UnaryHistory calculus ∧
    Cont operator spectrum projection ∧ Cont projection calculus endpoint ∧
      hsame provenance endpoint

theorem SpectralTheoremCarrier_classifier_transport
    {endpoint endpoint' operator spectrum projection calculus provenance : BHist} :
    SpectralTheoremCarrier endpoint operator spectrum projection calculus provenance ->
      hsame endpoint endpoint' ->
        SpectralTheoremCarrier endpoint' operator spectrum projection calculus endpoint' ∧
          Cont projection calculus endpoint' ∧ UnaryHistory endpoint' ∧
            hsame provenance endpoint' := by
  intro carrier sameEndpoint
  have transportedEndpoint : Cont projection calculus endpoint' :=
    cont_result_hsame_transport carrier.right.right.right.right.left sameEndpoint
  have projectionUnary : UnaryHistory projection :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.left
  have endpointUnary : UnaryHistory endpoint' :=
    unary_transport
      (unary_cont_closed projectionUnary carrier.right.right.left
        carrier.right.right.right.right.left)
      sameEndpoint
  have provenanceSame : hsame provenance endpoint' :=
    hsame_trans carrier.right.right.right.right.right sameEndpoint
  exact And.intro
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro transportedEndpoint (hsame_refl endpoint'))))))
    (And.intro transportedEndpoint (And.intro endpointUnary provenanceSame))

theorem SpectralTheoremOperator_measure_row_readback
    {operator spectralSide projection functional endpoint : BHist} :
    VecSpaceSingletonCarrier operator ->
      MeasureZeroBHistClassifier spectralSide BHist.Empty ->
        Cont spectralSide projection endpoint ->
          hsame projection BHist.Empty ->
            hsame functional endpoint ->
              VecSpaceSingletonCarrier operator ∧ MeasureZeroBHistCarrier spectralSide ∧
                MeasureZeroBHistClassifier projection BHist.Empty ∧
                  hsame functional endpoint ∧ UnaryHistory endpoint := by
  intro operatorCarrier spectralClassified projectionRow projectionEmpty sameFunctional
  have endpointEmpty : hsame endpoint BHist.Empty :=
    cont_respects_hsame spectralClassified.left projectionEmpty projectionRow
      (cont_left_unit BHist.Empty)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm endpointEmpty)
  have projectionClassified : MeasureZeroBHistClassifier projection BHist.Empty :=
    And.intro projectionEmpty (And.intro (hsame_refl BHist.Empty) projectionEmpty)
  exact And.intro operatorCarrier
    (And.intro spectralClassified.left
      (And.intro projectionClassified
        (And.intro sameFunctional endpointUnary)))

end BEDC.Derived.SpectralTheoremUp
