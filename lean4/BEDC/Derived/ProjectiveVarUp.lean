import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp

theorem ProjectiveVarBHistCarrier_chart_homogeneous_readback
    {AffPoint : BHist -> Prop} {PolyEvalZero : BHist -> BHist -> Prop}
    {family : ProbeBundle BHist} {chart endpoint homogeneousEval projectiveSpace : BHist} :
    AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero family chart ->
      PolynomialSingletonClassifier homogeneousEval BHist.Empty ->
        hsame projectiveSpace endpoint ->
          AffPoint chart ∧
            (forall {p : BHist}, InBundle p family -> PolyEvalZero p chart) ∧
              PolynomialSingletonCarrier homogeneousEval ∧
                PolynomialSingletonCarrier BHist.Empty ∧ hsame projectiveSpace endpoint := by
  intro chartLocus homogeneousClassified sameProjective
  exact And.intro chartLocus.left
    (And.intro chartLocus.right
      (And.intro homogeneousClassified.left
        (And.intro homogeneousClassified.right.left sameProjective)))

end BEDC.Derived.ProjectiveVarUp
