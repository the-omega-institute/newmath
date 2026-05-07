import BEDC.Derived.HilbertUp
import BEDC.Derived.MeasureUp

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.MeasureUp
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

end BEDC.Derived.SpectralTheoremUp
