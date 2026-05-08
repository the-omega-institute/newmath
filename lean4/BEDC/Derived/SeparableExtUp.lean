import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.FieldExtUp
open BEDC.Derived.PolynomialUp

def SeparableExtSourceRow
    (fieldExt polynomial base extension generator minimalPolynomial provenance : BHist) : Prop :=
  FieldExtSingletonCarrier fieldExt ∧
    PolynomialSingletonCarrier polynomial ∧
      FieldExtSingletonClassifier extension fieldExt ∧
        PolynomialSingletonClassifier minimalPolynomial polynomial ∧
          hsame base BHist.Empty ∧
            hsame generator extension ∧
              Cont extension minimalPolynomial provenance

theorem SeparableExtSourceRow_fieldext_polynomial_source
    {fieldExt polynomial base extension generator minimalPolynomial provenance : BHist} :
    SeparableExtSourceRow fieldExt polynomial base extension generator minimalPolynomial
        provenance ->
      FieldExtSingletonCarrier fieldExt ∧
        PolynomialSingletonCarrier polynomial ∧
          FieldExtSingletonClassifier extension fieldExt ∧
            PolynomialSingletonClassifier minimalPolynomial polynomial ∧
              Cont extension minimalPolynomial provenance := by
  intro row
  exact And.intro row.left
    (And.intro row.right.left
      (And.intro row.right.right.left
        (And.intro row.right.right.right.left row.right.right.right.right.right.right)))

end BEDC.Derived.SeparableExtUp
