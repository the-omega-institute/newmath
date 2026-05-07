import BEDC.Derived.DiffFormUp

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

end BEDC.Derived.DiffFormUp
