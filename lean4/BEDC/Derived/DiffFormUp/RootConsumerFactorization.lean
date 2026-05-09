import BEDC.Derived.DiffFormUp.RootConsumerFace
import BEDC.Derived.DiffFormUp.RootUnblockObligations

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootConsumerFactorization_wedge_derivative {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes left right : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger :
      BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus -> Cont degree dplus outDegree ->
            UnaryHistory rightLedger -> hsame ledger rightLedger -> UnaryHistory tensorLedger ->
              DiffFormWedgeProbeConcatenationLedger left right ledger rightLedger tensorLedger ->
                DegreeProbeAligned degree left -> DegreeProbeAligned dplus right ->
                  DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor
                      tensor scalar scalar antisym ledger ∧
                    DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger
                      tensorLedger ∧
                      DegreeProbeAligned outDegree (bundleAppend left right) ∧
                        hsame tensorLedger (append ledger rightLedger) := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor wedgeRoute rightLedgerUnary sameRightLedger tensorLedgerUnary
    probeLedger leftAligned rightAligned
  have routed :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
          degree probe tensor scalar antisym ledger ∧
        DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
          scalar scalar antisym ledger ∧
          DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger :=
    DiffFormRootConsumerPackage_operation_routing scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  have closure :
      DegreeProbeAligned outDegree (bundleAppend left right) ∧
        bundleLength (bundleAppend left right) = bundleLength left + bundleLength right ∧
          (forall probe : BHist,
            InBundle probe (bundleAppend left right) <-> InBundle probe left ∨
              InBundle probe right) ∧
            UnaryHistory outDegree ∧ hsame tensorLedger (append ledger rightLedger) ∧
              hsame ledger rightLedger :=
    DiffFormRootUnblock_wedge_cont_closure probeLedger routed.right.right leftAligned rightAligned
  exact And.intro routed.right.left
    (And.intro routed.right.right (And.intro closure.left closure.right.right.right.right.left))

end BEDC.Derived.DiffFormUp
