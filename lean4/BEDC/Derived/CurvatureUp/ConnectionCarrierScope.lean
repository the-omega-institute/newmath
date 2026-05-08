import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureBracketCarrier_connection_carrier_scope
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
        ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
          UnaryHistory base ∧ UnaryHistory fibre ∧ UnaryHistory sec ∧
            UnaryHistory tangentA ∧ UnaryHistory tangentB ∧ UnaryHistory derivativeA ∧
              UnaryHistory derivativeB ∧ Cont derivativeA derivativeB boundary ∧
                Cont boundary provenance curvatureLedger := by
  intro carrier
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.left
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.right.left
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.left.left
        (And.intro carrier.left.right.left
          (And.intro exactA.left
            (And.intro carrier.left.right.right.left
              (And.intro carrier.right.left.right.right.left
                (And.intro exactA.right.left
                  (And.intro exactB.right.left
                    (And.intro carrier.right.right.left carrier.right.right.right)))))))))

end BEDC.Derived.CurvatureUp
