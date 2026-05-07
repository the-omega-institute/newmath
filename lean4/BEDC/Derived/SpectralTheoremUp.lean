import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.MeasureUp
open BEDC.Derived.VecSpaceUp

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

end BEDC.Derived.SpectralTheoremUp
