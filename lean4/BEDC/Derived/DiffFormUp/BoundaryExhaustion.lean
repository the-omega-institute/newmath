import BEDC.Derived.DiffFormUp
import BEDC.Derived.DiffFormUp.AntisymmetryChain

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DiffFormBoundaryExhaustion_carrier_coverage {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
            UnaryHistory scalar ∧
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                ledger degree probe tensor scalar antisym ledger := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have coverage :=
    DiffFormRootDegreeClassifier_coverage (ScalarCarrier := ScalarCarrier)
      (ScalarClassifier := ScalarClassifier) scalarCert (probes := probes)
      (degree := degree) (probe := probe) (tensor := tensor) (scalar := scalar)
      (antisym := antisym) (ledger := ledger) probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute
  exact And.intro coverage.left.left
      (And.intro coverage.left.right.left
        (And.intro coverage.left.right.right.left
          (And.intro coverage.left.right.right.right.left coverage.right)))

theorem DiffFormBoundaryExhaustion_downstream_export
    {probes : ProbeBundle BHist}
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source chain degreeR
      probeR tensorR scalarR antisymR ledgerR : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
        scalar' antisym source ->
      DiffFormAntisymmetryChainLedger probes chain d probe tensor scalar antisym source degreeR
        probeR tensorR scalarR antisymR ledgerR ->
        UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus ∧
          UnaryHistory chain ∧ Cont d probe tensor ∧ Cont tensor antisym scalar ∧
            DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source degreeR
              probeR tensorR scalarR antisymR ledgerR := by
  intro derivativeLedger chainLedger
  have degreeRows := DiffFormExteriorDerivativeLedger_degree_raise derivativeLedger
  have chainRows := DiffFormAntisymmetryChainLedger_coverage chainLedger
  exact And.intro degreeRows.left
    (And.intro degreeRows.right.left
      (And.intro degreeRows.right.right
        (And.intro chainRows.left
          (And.intro chainRows.right.left
            (And.intro chainRows.right.right.left chainRows.right.right.right.right.right)))))

end BEDC.Derived.DiffFormUp
