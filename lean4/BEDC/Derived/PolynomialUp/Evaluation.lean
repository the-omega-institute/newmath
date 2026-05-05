import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Hist

theorem PolynomialZeroRemainder_singleton_classifier_self {t : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier t t ->
      PolynomialZeroRemainder t := by
  intro classified
  induction t with
  | nil =>
      exact PolynomialZeroRemainder.nil
  | cons x xs ih =>
      cases classified with
      | intro headClassified tailClassified =>
          exact PolynomialZeroRemainder.cons headClassified.left (ih tailClassified)

theorem PolynomialSingletonEval_zero_constant_term {a : BHist} {t : List BHist} :
    PolynomialSingletonCarrier a ->
      BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier t t ->
        PolynomialSingletonClassifier (PolynomialSingletonEval BHist.Empty (a :: t)) a := by
  intro carrierA classifiedTail
  exact PolynomialSingletonEval_zero_cons_constant carrierA
    (PolynomialZeroRemainder_singleton_classifier_self classifiedTail)

end BEDC.Derived.PolynomialUp
