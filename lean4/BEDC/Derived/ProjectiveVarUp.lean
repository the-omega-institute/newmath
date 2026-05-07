import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ProjectiveVarCarrier_scale_chart_transport
    {chart chart' point point' poly : BHist} {F : ProbeBundle BHist} :
    AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h chart)
        (fun p x : BHist =>
          PolynomialSingletonClassifier (PolynomialSingletonEval x [p]) BHist.Empty)
        F point ->
      PolynomialSingletonClassifier poly BHist.Empty ->
        hsame chart chart' ->
          hsame point point' ->
            InBundle poly F ->
              AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h chart')
                  (fun p x : BHist =>
                    PolynomialSingletonClassifier (PolynomialSingletonEval x [p]) BHist.Empty)
                  F point' ∧
                PolynomialSingletonClassifier (PolynomialSingletonEval point' [poly])
                  BHist.Empty := by
  intro locus polyZero sameChart samePoint polyMember
  have pointChart' : hsame point' chart' :=
    hsame_trans (hsame_symm samePoint) (hsame_trans locus.left sameChart)
  have evalPointPoly :
      PolynomialSingletonClassifier (PolynomialSingletonEval point [poly]) BHist.Empty :=
    locus.right polyMember
  have evalPointPolyParts :
      hsame poly BHist.Empty ∧ hsame (PolynomialSingletonMul point BHist.Empty) BHist.Empty :=
    append_eq_empty_iff.mp evalPointPoly.left
  have pointCarrier : PolynomialSingletonCarrier point :=
    (append_eq_empty_iff.mp evalPointPolyParts.right).left
  have point'Carrier : PolynomialSingletonCarrier point' :=
    hsame_trans (hsame_symm samePoint) pointCarrier
  have evalPoint'Poly :
      PolynomialSingletonClassifier (PolynomialSingletonEval point' [poly]) BHist.Empty := by
    have rowPoly : PolynomialSingletonClassifier (PolynomialSingletonEval point' [poly]) poly :=
      (PolynomialSingletonEval_singleton point'Carrier polyZero.left).left
    exact And.intro rowPoly.left
      (And.intro (hsame_refl BHist.Empty) (hsame_trans rowPoly.right.right polyZero.left))
  have transportedLocus :
      AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h chart')
        (fun p x : BHist =>
          PolynomialSingletonClassifier (PolynomialSingletonEval x [p]) BHist.Empty)
        F point' :=
    And.intro pointChart'
      (by
        intro p memberP
        have evalPointP :
            PolynomialSingletonClassifier (PolynomialSingletonEval point [p]) BHist.Empty :=
          locus.right memberP
        have evalPointPParts :
            hsame p BHist.Empty ∧
              hsame (PolynomialSingletonMul point (PolynomialSingletonEval point []))
                BHist.Empty :=
          append_eq_empty_iff.mp evalPointP.left
        have rowP : PolynomialSingletonClassifier (PolynomialSingletonEval point' [p]) p :=
          (PolynomialSingletonEval_singleton point'Carrier evalPointPParts.left).left
        exact And.intro rowP.left
          (And.intro (hsame_refl BHist.Empty)
            (hsame_trans rowP.right.right evalPointPParts.left)))
  exact And.intro transportedLocus evalPoint'Poly

end BEDC.Derived.ProjectiveVarUp
