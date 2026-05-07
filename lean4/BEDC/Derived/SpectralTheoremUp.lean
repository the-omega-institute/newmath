import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.MeasureUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.SpectralTheoremUp
