import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.MeasureUp
open BEDC.Derived.VecSpaceUp

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
