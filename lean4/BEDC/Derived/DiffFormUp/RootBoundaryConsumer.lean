import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootBoundaryConsumer_exactness {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger :
      BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus -> Cont degree dplus outDegree ->
            UnaryHistory rightLedger -> hsame ledger rightLedger -> UnaryHistory tensorLedger ->
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                  ledger degree probe tensor scalar antisym ledger ∧
                DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor
                  tensor scalar scalar antisym ledger ∧
                  DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger
                    tensorLedger ∧
                    UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
                      UnaryHistory scalar := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor wedgeRoute rightLedgerUnary sameRightLedger tensorLedgerUnary
  have routed :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
          degree probe tensor scalar antisym ledger ∧
        DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
          scalar scalar antisym ledger ∧
          DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger :=
    DiffFormRootConsumerPackage_operation_routing scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact And.intro routed.left
    (And.intro routed.right.left
      (And.intro routed.right.right
        (And.intro carrierRows.left
          (And.intro carrierRows.right.left
            (And.intro carrierRows.right.right.left carrierRows.right.right.right.left)))))

end BEDC.Derived.DiffFormUp
