import BEDC.Derived.LambdaCalcUp.NameCertCarrierObligation
import BEDC.Derived.LambdaCalcUp.PublicBoundary

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem LambdaCalcUp_StdBridge
    {graph edge connected acyclic tag payload endpoint alphaEndpoint betaEndpoint alphaLedger
      betaLedger publicLedger pkgLedger : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload alphaEndpoint ->
        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload betaEndpoint ->
          Cont endpoint alphaEndpoint alphaLedger ->
            Cont endpoint betaEndpoint betaLedger ->
              Cont alphaLedger betaLedger publicLedger ->
                Cont publicLedger tag pkgLedger ->
                  SemanticNameCert
                      (fun row : BHist =>
                        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag
                          payload row)
                      (fun row : BHist =>
                        hsame row endpoint ∨ hsame row alphaEndpoint ∨
                          hsame row betaEndpoint ∨ hsame row publicLedger)
                      (fun row : BHist =>
                        UnaryHistory row ∧
                          (hsame row endpoint ∨ hsame row alphaEndpoint ∨
                            hsame row betaEndpoint ∨ hsame row publicLedger))
                      hsame ∧
                    UnaryHistory publicLedger ∧
                      hsame publicLedger (append alphaLedger betaLedger) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet alphaPacket betaPacket alphaLedgerRow betaLedgerRow publicLedgerRow
    pkgLedgerRow
  have publicBoundary :=
    LambdaCalcBHistTermPacketCarrier_public_boundary packet alphaPacket betaPacket
      alphaLedgerRow betaLedgerRow publicLedgerRow
  have _pkgLedgerReadback : hsame pkgLedger (append publicLedger tag) :=
    pkgLedgerRow
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row alphaEndpoint ∨ hsame row betaEndpoint ∨
              hsame row publicLedger)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row endpoint ∨ hsame row alphaEndpoint ∨ hsame row betaEndpoint ∨
                hsame row publicLedger))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint packet
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          (LambdaCalcBHistTermPacketCarrier_public_endpoint_transport source
            (hsame_refl tag) sameRows).left
    }
    pattern_sound := by
      intro _row source
      exact Or.inl (cont_deterministic source.right.right.right packet.right.right.right)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right.right.left,
          Or.inl (cont_deterministic source.right.right.right packet.right.right.right)⟩
  }
  exact ⟨cert, publicBoundary.left, publicLedgerRow⟩

end BEDC.Derived.LambdaCalcUp
