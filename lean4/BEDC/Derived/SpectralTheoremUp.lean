import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.MeasureUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SpectralTheoremSingleton_carrier_classifier_obligation
    {operator spectral measured projection calculus : BHist} :
    VecSpaceSingletonCarrier operator ->
      MeasureZeroBHistCarrier measured ->
        hsame spectral BHist.Empty ->
          Cont operator measured projection ->
            Cont projection spectral calculus ->
              VecSpaceSingletonCarrier operator ∧
                MeasureZeroBHistClassifier measured BHist.Empty ∧
                  UnaryHistory projection ∧ UnaryHistory calculus ∧
                    Cont operator measured projection ∧
                      Cont projection spectral calculus := by
  intro operatorCarrier measuredCarrier spectralEmpty operatorMeasured projectionSpectral
  have operatorUnary : UnaryHistory operator :=
    unary_transport unary_empty (hsame_symm operatorCarrier)
  have measuredUnary : UnaryHistory measured :=
    unary_transport unary_empty (hsame_symm measuredCarrier)
  have projectionUnary : UnaryHistory projection :=
    unary_cont_closed operatorUnary measuredUnary operatorMeasured
  have spectralUnary : UnaryHistory spectral :=
    unary_transport unary_empty (hsame_symm spectralEmpty)
  have calculusUnary : UnaryHistory calculus :=
    unary_cont_closed projectionUnary spectralUnary projectionSpectral
  have measuredClassified : MeasureZeroBHistClassifier measured BHist.Empty :=
    And.intro measuredCarrier (And.intro (hsame_refl BHist.Empty) measuredCarrier)
  exact And.intro operatorCarrier
    (And.intro measuredClassified
      (And.intro projectionUnary
        (And.intro calculusUnary
          (And.intro operatorMeasured projectionSpectral))))

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

theorem SpectralTheoremEmptySpectrum_calculus_endpoint
    {operator projection spectrum calculus endpoint : BHist} :
    VecSpaceSingletonCarrier operator ->
      HilbertSingletonProjectionWitness operator projection ->
        hsame spectrum BHist.Empty ->
          hsame calculus BHist.Empty ->
            Cont spectrum calculus endpoint ->
              VecSpaceSingletonClassifier projection BHist.Empty ∧
                MeasureZeroBHistClassifier spectrum BHist.Empty ∧
                  MeasureZeroBHistCarrier endpoint := by
  intro _operatorCarrier projectionWitness spectrumEmpty calculusEmpty spectralRow
  have endpointEmpty : hsame endpoint BHist.Empty :=
    cont_respects_hsame spectrumEmpty calculusEmpty spectralRow (cont_left_unit BHist.Empty)
  have spectrumClassified : MeasureZeroBHistClassifier spectrum BHist.Empty :=
    And.intro spectrumEmpty (And.intro (hsame_refl BHist.Empty) spectrumEmpty)
  exact And.intro projectionWitness.right.right.left
    (And.intro spectrumClassified endpointEmpty)

theorem SpectralTheoremProjectionMeasure_functional_calculus_empty
    {op projection spectrum pvm calculus endpoint : BHist} :
    HilbertSingletonProjectionWitness op projection ->
      MeasureZeroBHistClassifier spectrum BHist.Empty ->
        MeasureZeroBHistClassifier pvm BHist.Empty ->
          MeasureZeroBHistClassifier calculus BHist.Empty ->
            Cont spectrum pvm endpoint ->
              VecSpaceSingletonClassifier projection BHist.Empty ∧
                MeasureZeroBHistClassifier endpoint BHist.Empty ∧
                  MeasureZeroBHistClassifier calculus endpoint := by
  intro projectionWitness spectrumZero pvmZero calculusZero spectrumPvm
  have endpointZero : MeasureZeroBHistCarrier endpoint :=
    cont_respects_hsame spectrumZero.left pvmZero.left spectrumPvm
      (cont_left_unit BHist.Empty)
  have endpointClassified : MeasureZeroBHistClassifier endpoint BHist.Empty :=
    And.intro endpointZero (And.intro (hsame_refl BHist.Empty) endpointZero)
  have calculusEndpointSame : hsame calculus endpoint :=
    hsame_trans calculusZero.left (hsame_symm endpointZero)
  have calculusEndpoint : MeasureZeroBHistClassifier calculus endpoint :=
    And.intro calculusZero.left (And.intro endpointZero calculusEndpointSame)
  exact And.intro projectionWitness.right.right.left
    (And.intro endpointClassified calculusEndpoint)

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
