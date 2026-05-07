import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ProjectiveVarVisibleCarrier_endpoint_exactness
    {family : ProbeBundle BHist} {chart homogeneous projectiveSpace zeroEval endpoint : BHist} :
    AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
        (fun poly point : BHist => PolynomialSingletonClassifier poly point) family chart ->
      PolynomialSingletonClassifier homogeneous BHist.Empty ->
        hsame projectiveSpace chart ->
          Cont projectiveSpace zeroEval endpoint ->
            hsame zeroEval BHist.Empty ->
              hsame endpoint chart ∧
                AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
                  (fun poly point : BHist => PolynomialSingletonClassifier poly point)
                  family endpoint := by
  intro chartLocus _homogeneousZero sameProjectiveSpace endpointRow zeroEvalEmpty
  have endpointProjective : hsame endpoint projectiveSpace :=
    cont_right_unit_result (by
      cases zeroEvalEmpty
      exact endpointRow)
  have endpointChart : hsame endpoint chart :=
    hsame_trans endpointProjective sameProjectiveSpace
  have endpointEmpty : hsame endpoint BHist.Empty :=
    hsame_trans endpointChart chartLocus.left
  have endpointLocus :
      AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
        (fun poly point : BHist => PolynomialSingletonClassifier poly point) family endpoint :=
    And.intro endpointEmpty
      (by
        intro p member
        have chartClassified : PolynomialSingletonClassifier p chart :=
          chartLocus.right member
        have endpointClassified : PolynomialSingletonClassifier p endpoint :=
          And.intro chartClassified.left
            (And.intro endpointEmpty
              (hsame_trans chartClassified.right.right (hsame_symm endpointChart)))
        exact endpointClassified)
  exact And.intro endpointChart endpointLocus

end BEDC.Derived.ProjectiveVarUp
