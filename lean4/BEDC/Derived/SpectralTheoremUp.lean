import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.MeasureUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.SpectralTheoremUp
