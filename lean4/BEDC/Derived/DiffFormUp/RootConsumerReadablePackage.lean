import BEDC.Derived.DiffFormUp.RootNameCertSurface

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootConsumerPackage_namecert_boundary {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger :
      BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus -> Cont degree dplus outDegree ->
            UnaryHistory rightLedger -> hsame ledger rightLedger -> UnaryHistory tensorLedger ->
              SemanticNameCert
                  (fun raised : BHist =>
                    DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe
                      tensor tensor scalar scalar antisym ledger)
                  (fun raised : BHist =>
                    DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe
                      tensor tensor scalar scalar antisym ledger)
                  (fun raised : BHist =>
                    DiffFormExteriorDerivativeLedger scalar raised degree raised probe probe
                      tensor tensor scalar scalar antisym ledger)
                  hsame ∧
                DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                    ledger degree probe tensor scalar antisym ledger ∧
                  DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor
                      tensor scalar scalar antisym ledger ∧
                    DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger
                        tensorLedger ∧
                      (hsame dplus BHist.Empty -> False) := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor wedgeRoute rightLedgerUnary sameRightLedger tensorLedgerUnary
  have surface :=
    DiffFormRootNameCert_surface scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  have routed :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
          degree probe tensor scalar antisym ledger ∧
        DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
          scalar scalar antisym ledger ∧
          DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger :=
    DiffFormRootConsumerPackage_operation_routing scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  have boundaryRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty routed.right.left
  exact And.intro surface.left
    (And.intro routed.left
      (And.intro routed.right.left
        (And.intro routed.right.right boundaryRows.right.right.right)))

end BEDC.Derived.DiffFormUp
