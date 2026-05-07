import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ProjectiveVarCarrier_obligation_rows
    {point polynomial eval package endpoint : BHist} {family : ProbeBundle BHist} :
    AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
        (fun p x : BHist =>
          PolynomialSingletonClassifier p BHist.Empty ∧ hsame x BHist.Empty)
        family point ->
      PolynomialSingletonClassifier polynomial BHist.Empty ->
        InBundle polynomial family ->
          Cont point polynomial eval ->
            hsame package eval ->
              UnaryHistory point ∧ PolynomialSingletonCarrier polynomial ∧
                PolynomialSingletonClassifier eval BHist.Empty ∧ hsame package BHist.Empty := by
  intro locus polynomialClassified memberPolynomial evalRow packageEval
  have pointEmpty : hsame point BHist.Empty := locus.left
  have pointUnary : UnaryHistory point :=
    unary_transport unary_empty (hsame_symm pointEmpty)
  have equationRow :
      PolynomialSingletonClassifier polynomial BHist.Empty ∧ hsame point BHist.Empty :=
    locus.right memberPolynomial
  have evalClassified : PolynomialSingletonClassifier eval BHist.Empty :=
    PolynomialSingletonClassifier_cont_result_empty_classified pointEmpty
      equationRow.left.left evalRow
  have packageEmpty : hsame package BHist.Empty :=
    hsame_trans packageEval evalClassified.left
  exact And.intro pointUnary
    (And.intro polynomialClassified.left (And.intro evalClassified packageEmpty))

end BEDC.Derived.ProjectiveVarUp
