import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp

theorem ProjectiveVarHomogeneousZeroLocus_visible_package
    {F : ProbeBundle BHist} {x scale projectiveEndpoint : BHist} :
    AffineFiniteFamilyZeroLocus PolynomialSingletonCarrier PolynomialSingletonClassifier F x ->
      PolynomialSingletonCarrier scale ->
        Cont x scale projectiveEndpoint ->
          PolynomialSingletonCarrier projectiveEndpoint ∧
            AffineFiniteFamilyZeroLocus PolynomialSingletonCarrier PolynomialSingletonClassifier F
              projectiveEndpoint := by
  intro locus scaleCarrier projectiveRow
  have xCarrier : PolynomialSingletonCarrier x := locus.left
  have endpointCarrier : PolynomialSingletonCarrier projectiveEndpoint :=
    cont_respects_hsame xCarrier scaleCarrier projectiveRow (cont_right_unit BHist.Empty)
  have xEndpointClassified : PolynomialSingletonClassifier x projectiveEndpoint :=
    And.intro xCarrier
      (And.intro endpointCarrier (hsame_trans xCarrier (hsame_symm endpointCarrier)))
  have endpointRows :
      forall {p : BHist}, InBundle p F ->
        PolynomialSingletonClassifier p projectiveEndpoint := by
    intro p member
    exact And.intro (locus.right member).left
      (And.intro endpointCarrier
        (hsame_trans (locus.right member).left (hsame_symm endpointCarrier)))
  exact And.intro endpointCarrier (And.intro endpointCarrier endpointRows)

end BEDC.Derived.ProjectiveVarUp
