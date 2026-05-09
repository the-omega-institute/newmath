import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureBracketCarrier_bundle_fibre_dependency_row
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
        ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
          UnaryHistory fibre ∧ UnaryHistory sec ∧ UnaryHistory ledgerA ∧ UnaryHistory ledgerB ∧
            hsame boundary (append derivativeA derivativeB) := by
  intro carrier
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.left
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.right.left
  exact
    ⟨carrier.left, carrier.right.left, carrier.left.right.left, exactA.left,
      exactA.right.right.left, exactB.right.right.left, carrier.right.right.left⟩

end BEDC.Derived.CurvatureUp
