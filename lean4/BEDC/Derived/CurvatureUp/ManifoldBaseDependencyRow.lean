import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureBracketCarrier_manifold_base_dependency_row
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger tangentPair : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont tangentA tangentB tangentPair ->
        UnaryHistory base ∧ UnaryHistory tangentA ∧ UnaryHistory tangentB ∧
          UnaryHistory tangentPair ∧ hsame tangentPair (append tangentA tangentB) ∧
            hsame ledgerA (append (append (append base fibre) tangentA) provenance) ∧
              hsame ledgerB (append (append (append base fibre) tangentB) provenance) ∧
                hsame curvatureLedger (append boundary provenance) := by
  intro carrier tangentPairRow
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.left
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation carrier.right.left
  have boundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  have tangentPairUnary : UnaryHistory tangentPair :=
    unary_cont_closed carrier.left.right.right.left carrier.right.left.right.right.left
      tangentPairRow
  exact And.intro carrier.left.left
    (And.intro carrier.left.right.right.left
      (And.intro carrier.right.left.right.right.left
        (And.intro tangentPairUnary
          (And.intro tangentPairRow
            (And.intro exactA.right.right.right.right.right
              (And.intro exactB.right.right.right.right.right
                boundaryRows.right.right.right))))))

end BEDC.Derived.CurvatureUp
