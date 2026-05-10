import BEDC.Derived.DiffFormUp
import BEDC.Derived.DiffFormUp.AntisymmetryChain
import BEDC.Derived.DiffFormUp.ConsumerBoundary

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

theorem DiffFormDownstreamBoundary_exhaustion {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {probes : ProbeBundle BHist}
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source chain degreeR
      probeR tensorR scalarR antisymR ledgerR outDegree rightLedger tensorLedger : BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
      DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
        scalar' antisym source ->
      DiffFormAntisymmetryChainLedger probes chain d probe tensor scalar antisym source degreeR
        probeR tensorR scalarR antisymR ledgerR ->
      DiffFormWedgeDegreeLedger d dplus outDegree source rightLedger tensorLedger ->
        DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source degreeR probeR
            tensorR scalarR antisymR ledgerR ∧
          DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
            scalar' antisym source ∧
          DiffFormWedgeDegreeLedger d dplus outDegree source rightLedger tensorLedger ∧
          UnaryHistory chain ∧ UnaryHistory outDegree ∧ Cont d (BHist.e1 BHist.Empty) dplus ∧
            (hsame dplus BHist.Empty -> False) := by
  intro probeIn scalarCarrier derivativeLedger chainLedger wedgeLedger
  have _scalarCert : NameCert ScalarCarrier ScalarClassifier := scalarCert
  have exported :=
    DiffFormBoundaryExhaustion_downstream_export derivativeLedger chainLedger
  have wedgeBoundary :=
    DiffFormWedgeDegreeLedger_consumer_boundary wedgeLedger (hsame_refl d) (hsame_refl dplus)
      (hsame_refl outDegree)
  have successorRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty derivativeLedger
  exact
    ⟨exported.right.right.right.right.right.right,
      derivativeLedger,
      wedgeBoundary.right.right.right.right.left,
      exported.right.right.right.left,
      wedgeBoundary.right.right.left,
      exported.right.right.left,
      successorRows.right.right.right⟩

end BEDC.Derived.DiffFormUp
