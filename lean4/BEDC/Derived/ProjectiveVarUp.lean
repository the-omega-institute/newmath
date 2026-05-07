import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

theorem ProjectiveVarFiniteChartCarrier_endpoint_transport
    {F : ProbeBundle BHist} {x endpoint : BHist} :
    AffineFiniteFamilyZeroLocus PolynomialSingletonCarrier PolynomialSingletonClassifier F x ->
      PolynomialSingletonClassifier endpoint BHist.Empty ->
        hsame endpoint x ->
          AffineFiniteFamilyZeroLocus PolynomialSingletonCarrier PolynomialSingletonClassifier F endpoint ∧
            PolynomialSingletonClassifier x endpoint ∧
              (forall {p : BHist}, InBundle p F ->
                PolynomialSingletonClassifier p endpoint) := by
  intro locus endpointZero sameEndpointX
  have endpointCarrier : PolynomialSingletonCarrier endpoint :=
    endpointZero.left
  have xCarrier : PolynomialSingletonCarrier x :=
    locus.left
  have endpointLocus :
      AffineFiniteFamilyZeroLocus PolynomialSingletonCarrier PolynomialSingletonClassifier F
        endpoint := by
    exact And.intro endpointCarrier
      (by
        intro p member
        have rowPX : PolynomialSingletonClassifier p x := locus.right member
        have pCarrier : PolynomialSingletonCarrier p := rowPX.left
        have samePEndpoint : hsame p endpoint :=
          hsame_trans pCarrier (hsame_symm endpointCarrier)
        exact And.intro pCarrier (And.intro endpointCarrier samePEndpoint))
  have xEndpoint : PolynomialSingletonClassifier x endpoint :=
    And.intro xCarrier (And.intro endpointCarrier (hsame_symm sameEndpointX))
  exact And.intro endpointLocus
    (And.intro xEndpoint
      (by
        intro p member
        exact endpointLocus.right member))

end BEDC.Derived.ProjectiveVarUp
