import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.StatManifoldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def StatManifoldDependencyLedgerPacket
    (manifold fisher metric connection dualConnection provenance ledger : BHist) : Prop :=
  Cont manifold fisher metric ∧ Cont metric connection ledger ∧
    Cont ledger dualConnection provenance

theorem StatManifoldDependencyLedgerPacket_public_projection
    {manifold fisher metric connection dualConnection provenance ledger : BHist} :
    StatManifoldDependencyLedgerPacket manifold fisher metric connection dualConnection provenance
      ledger ->
      hsame metric (append manifold fisher) ∧ hsame ledger (append metric connection) ∧
        hsame provenance (append ledger dualConnection) ∧
          SemanticNameCert (fun row : BHist => row = ledger)
            (fun row : BHist => row = ledger)
            (fun row : BHist => row = ledger) hsame := by
  intro packet
  cases packet with
  | intro metricRow packetRest =>
      cases packetRest with
      | intro ledgerRow provenanceRow =>
          constructor
          · exact metricRow
          · constructor
            · exact ledgerRow
            · constructor
              · exact provenanceRow
              · exact {
                  core := {
                    carrier_inhabited := ⟨ledger, rfl⟩
                    equiv_refl := by
                      intro row _source
                      exact hsame_refl row
                    equiv_symm := by
                      intro _row _row' same
                      exact hsame_symm same
                    equiv_trans := by
                      intro _row _row' _row'' sameLeft sameRight
                      exact hsame_trans sameLeft sameRight
                    carrier_respects_equiv := by
                      intro _row _row' same source
                      exact (hsame_symm same).trans source
                  }
                  pattern_sound := by
                    intro _row source
                    exact source
                  ledger_sound := by
                    intro _row source
                    exact source
                }

end BEDC.Derived.StatManifoldUp
