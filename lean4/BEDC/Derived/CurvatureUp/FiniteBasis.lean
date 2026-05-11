import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureBracketCarrier_finite_basis
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
        ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
          Cont derivativeA derivativeB boundary ∧ Cont boundary provenance curvatureLedger ∧
            UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
              hsame boundary (append derivativeA derivativeB) ∧
                hsame curvatureLedger (append boundary provenance) ∧
                  SemanticNameCert
                    (fun e : BHist =>
                      exists b : BHist,
                        CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA
                          derivativeB provenance ledgerA ledgerB b e)
                    (fun e : BHist =>
                      exists b : BHist,
                        CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA
                          derivativeB provenance ledgerA ledgerB b e)
                    (fun e : BHist =>
                      exists b : BHist,
                        CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA
                          derivativeB provenance ledgerA ledgerB b e)
                    (fun left right : BHist =>
                      (exists lb : BHist,
                        CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA
                          derivativeB provenance ledgerA ledgerB lb left) ∧
                        (exists rb : BHist,
                          CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA
                            derivativeB provenance ledgerA ledgerB rb right) ∧
                          hsame left right) := by
  intro carrier
  have rows :=
    CurvatureBracketCarrier_source_row_coverage carrier
  have cert :=
    CurvatureBracketCarrier_semantic_name_certificate carrier
  exact
    ⟨rows.left,
      rows.right.left,
      rows.right.right.left,
      rows.right.right.right.left,
      rows.right.right.right.right.left,
      rows.right.right.right.right.right.left,
      rows.right.right.right.right.right.right.left,
      rows.right.right.right.right.right.right.right,
      cert⟩

end BEDC.Derived.CurvatureUp
