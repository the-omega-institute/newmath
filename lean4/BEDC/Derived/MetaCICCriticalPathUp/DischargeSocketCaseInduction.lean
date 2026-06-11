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

theorem MetaCICCriticalPathDischargeSocketCaseInduction [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName filledRead openRead checkerRead l10ResidualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff dischargeSocket filledRead →
        Cont obstruction dischargeSocket openRead →
          Cont handoff transport checkerRead →
            Cont dischargeSocket route l10ResidualRead →
              PkgSig bundle filledRead pkg →
                PkgSig bundle openRead pkg →
                  PkgSig bundle checkerRead pkg →
                    PkgSig bundle l10ResidualRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row filledRead ∨ hsame row openRead ∨
                                hsame row checkerRead ∨ hsame row l10ResidualRead) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row dischargeSocket ∨ hsame row obstruction ∨
                              hsame row handoff ∨ hsame row transport ∨ hsame row route ∨
                                hsame row filledRead ∨ hsame row openRead ∨
                                  hsame row checkerRead ∨ hsame row l10ResidualRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle filledRead pkg ∧
                              PkgSig bundle openRead pkg ∧ PkgSig bundle checkerRead pkg ∧
                                PkgSig bundle l10ResidualRead pkg)
                          hsame ∧
                        UnaryHistory filledRead ∧ UnaryHistory openRead ∧
                          UnaryHistory checkerRead ∧ UnaryHistory l10ResidualRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffSocketFilled obstructionSocketOpen handoffTransportChecker
    socketRouteResidual filledPkg openPkg checkerPkg residualPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have filledUnary : UnaryHistory filledRead :=
    unary_cont_closed handoffUnary dischargeSocketUnary handoffSocketFilled
  have openUnary : UnaryHistory openRead :=
    unary_cont_closed obstructionUnary dischargeSocketUnary obstructionSocketOpen
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed handoffUnary transportUnary handoffTransportChecker
  have residualUnary : UnaryHistory l10ResidualRead :=
    unary_cont_closed dischargeSocketUnary routeUnary socketRouteResidual
  have sourceFilled :
      (fun row : BHist =>
        (hsame row filledRead ∨ hsame row openRead ∨ hsame row checkerRead ∨
            hsame row l10ResidualRead) ∧
          UnaryHistory row) filledRead := by
    exact ⟨Or.inl (hsame_refl filledRead), filledUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row filledRead ∨ hsame row openRead ∨ hsame row checkerRead ∨
                hsame row l10ResidualRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dischargeSocket ∨ hsame row obstruction ∨ hsame row handoff ∨
              hsame row transport ∨ hsame row route ∨ hsame row filledRead ∨
                hsame row openRead ∨ hsame row checkerRead ∨ hsame row l10ResidualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle filledRead pkg ∧
              PkgSig bundle openRead pkg ∧ PkgSig bundle checkerRead pkg ∧
                PkgSig bundle l10ResidualRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro filledRead sourceFilled
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
        constructor
        · cases source.left with
          | inl sameFilled =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFilled)
          | inr rest =>
              cases rest with
              | inl sameOpen =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameOpen))
              | inr rest =>
                  cases rest with
                  | inl sameChecker =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameChecker)))
                  | inr sameResidual =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameResidual)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFilled =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFilled)))))
      | inr rest =>
          cases rest with
          | inl sameOpen =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameOpen))))))
          | inr rest =>
              cases rest with
              | inl sameChecker =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl sameChecker)))))))
              | inr sameResidual =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr sameResidual)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, filledPkg, openPkg, checkerPkg, residualPkg⟩
  }
  exact ⟨cert, filledUnary, openUnary, checkerUnary, residualUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
