import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ComplexHistoryClassifier_component_classifier_unary_context_positive_components
    {p p' real imag real' imag' h k q q' : BHist} :
    UnaryHistory p -> hsame p p' -> RatUp.RatHistoryClassifier real real' ->
      RatUp.RatHistoryClassifier imag imag' -> Cont real imag h -> Cont real' imag' k ->
        UnaryHistory q -> hsame q q' ->
          ∃ hr hi kr ki : BHist,
            RatUp.RatHistoryCarrier hr ∧ RatUp.RatHistoryCarrier hi ∧
              RatUp.RatHistoryCarrier kr ∧ RatUp.RatHistoryCarrier ki ∧
                Cont hr hi (append p (append h q)) ∧
                  Cont kr ki (append p' (append k q')) ∧
                    hsame (append p (append h q)) (append p' (append k q')) ∧
                      RatUp.PositiveUnaryDenominator hr ∧
                        RatUp.PositiveUnaryDenominator hi ∧
                          RatUp.PositiveUnaryDenominator kr ∧
                            RatUp.PositiveUnaryDenominator ki := by
  intro pUnary sameP realClass imagClass contH contK qUnary sameQ
  have contextClassified :
      ComplexHistoryClassifier (append p (append h q)) (append p' (append k q')) :=
    ComplexHistoryClassifier_component_classifier_unary_context_intro
      pUnary sameP realClass imagClass contH contK qUnary sameQ
  exact ComplexHistoryClassifier_positive_components contextClassified

end BEDC.Derived.ComplexUp
