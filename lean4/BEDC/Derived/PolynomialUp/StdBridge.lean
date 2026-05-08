import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PolynomialUp_StdBridge :
    SemanticNameCert PolynomialSingletonCarrier PolynomialSingletonCarrier
        PolynomialSingletonCarrier PolynomialSingletonClassifier ∧
      PolynomialSingletonCarrier PolynomialSingletonZero ∧
      PolynomialSingletonCarrier PolynomialSingletonOne ∧
      (forall {P Q : BHist}, PolynomialSingletonCarrier P -> PolynomialSingletonCarrier Q ->
        PolynomialSingletonCarrier (PolynomialSingletonAdd P Q) ∧
          PolynomialSingletonCarrier (PolynomialSingletonMul P Q)) ∧
      (forall {P : BHist}, PolynomialSingletonCarrier P ->
        PolynomialSingletonClassifier
          (PolynomialSingletonNormalize (PolynomialSingletonNormalize P))
          (PolynomialSingletonNormalize P)) := by
  have laws := singleton_empty_history_polynomial_laws
  constructor
  · exact laws.left
  · constructor
    · exact laws.right.left
    · constructor
      · exact laws.right.right.left
      · constructor
        · exact laws.right.right.right.right.left
        · exact laws.right.right.right.left

end BEDC.Derived.PolynomialUp
