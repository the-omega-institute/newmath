import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem PolynomialSingletonRawMul_left_distributes_over_raw_add {P Q R : BHist} :
    PolynomialSingletonCarrier P -> PolynomialSingletonCarrier Q -> PolynomialSingletonCarrier R ->
      PolynomialSingletonClassifier (PolynomialSingletonMul P (PolynomialSingletonAdd Q R))
        (PolynomialSingletonAdd (PolynomialSingletonMul P Q) (PolynomialSingletonMul P R)) ∧
      hsame (PolynomialSingletonMul P (PolynomialSingletonAdd Q R)) (append P (append Q R)) := by
  intro carrierP carrierQ carrierR
  have classified :=
    (PolynomialSingleton_append_distrib_classified carrierP carrierQ carrierR).left
  exact And.intro classified (hsame_refl (append P (append Q R)))

end BEDC.Derived.PolynomialUp
