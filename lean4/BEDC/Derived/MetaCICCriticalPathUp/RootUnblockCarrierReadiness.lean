import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRootUnblockCarrierReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName source localCert openNode unblock dischargeRow transportRow continuationRow
      packageRow ledgerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      UnaryHistory source →
        UnaryHistory localCert →
          UnaryHistory unblock →
            Cont source localCert openNode →
              Cont openNode unblock dischargeRow →
                UnaryHistory transportRow →
                  UnaryHistory continuationRow →
                    Cont transportRow continuationRow ledgerRow →
                      PkgSig bundle packageRow pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row ledgerRow ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row localCert ∨ hsame row openNode ∨
                                hsame row unblock ∨ hsame row dischargeRow ∨
                                  hsame row transportRow ∨ hsame row continuationRow ∨
                                    hsame row packageRow ∨ hsame row ledgerRow)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle packageRow pkg ∧
                                (hsame row ledgerRow ∨ hsame row dischargeRow))
                            hsame ∧
                          UnaryHistory openNode ∧ UnaryHistory dischargeRow ∧
                            UnaryHistory ledgerRow := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet sourceUnary localCertUnary unblockUnary sourceLocalOpen openUnblockDischarge
    transportUnary continuationUnary transportContinuationLedger packagePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportPacketUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalRoute, _handoffObstructionSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have openNodeUnary : UnaryHistory openNode :=
    unary_cont_closed sourceUnary localCertUnary sourceLocalOpen
  have dischargeRowUnary : UnaryHistory dischargeRow :=
    unary_cont_closed openNodeUnary unblockUnary openUnblockDischarge
  have ledgerRowUnary : UnaryHistory ledgerRow :=
    unary_cont_closed transportUnary continuationUnary transportContinuationLedger
  have sourceLedger :
      (fun row : BHist => hsame row ledgerRow ∧ UnaryHistory row) ledgerRow := by
    exact ⟨hsame_refl ledgerRow, ledgerRowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row localCert ∨ hsame row openNode ∨
              hsame row unblock ∨ hsame row dischargeRow ∨ hsame row transportRow ∨
                hsame row continuationRow ∨ hsame row packageRow ∨ hsame row ledgerRow)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle packageRow pkg ∧
              (hsame row ledgerRow ∨ hsame row dischargeRow))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRow sourceLedger
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, packagePkg, Or.inl source.left⟩
  }
  exact ⟨cert, openNodeUnary, dischargeRowUnary, ledgerRowUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
