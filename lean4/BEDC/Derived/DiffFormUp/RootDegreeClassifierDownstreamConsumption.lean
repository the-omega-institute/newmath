import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormRootDegreeClassifier_downstream_consumption
    {omega domega degree raised probe probePrime tensor tensorPrime scalar scalarPrime antisym
      source degree2 probe2 tensor2 scalar2 antisym2 source2 raised2 : BHist}
    {bundle : ProbeBundle BHist} :
    DiffFormExteriorDerivativeLedger omega domega degree raised probe probePrime tensor
        tensorPrime scalar scalarPrime antisym source ->
      DiffFormBHistClassifier hsame bundle degree probe tensor scalar antisym source degree2
        probe2 tensor2 scalar2 antisym2 source2 ->
        DegreeProbeAligned degree bundle ->
          (UnaryHistory degree ∧ InBundle probe bundle ∧ UnaryHistory tensor ∧
            UnaryHistory scalar ∧
              hsame source (append degree (append probe (append tensor (append scalar antisym))))) ->
            hsame raised raised2 ->
              DegreeProbeAligned degree2 bundle ∧ UnaryHistory degree2 ∧ InBundle probe2 bundle ∧
                UnaryHistory tensor2 ∧ UnaryHistory scalar2 ∧
                  Cont degree2 (BHist.e1 BHist.Empty) raised2 := by
  intro ledger classified aligned support sameRaised
  have stable :=
    DiffFormRootDegreeProbeFace_stability classified aligned support
  have degreeRows :=
    DiffFormExteriorDerivativeLedger_degree_raise ledger
  have degreeSame : hsame degree degree2 := classified.right.right.left
  have raisedCont : Cont degree2 (BHist.e1 BHist.Empty) raised2 := by
    cases degreeSame
    cases sameRaised
    exact degreeRows.right.right
  exact And.intro stable.left
    (And.intro stable.right.left
      (And.intro stable.right.right.left
        (And.intro stable.right.right.right.left
          (And.intro stable.right.right.right.right.left raisedCont))))

end BEDC.Derived.DiffFormUp
