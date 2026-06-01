import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualConfluenceBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff dischargeSocket residualRead →
        PkgSig bundle residualRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row residualRead ∨
                  hsame row obstruction)
              (fun row : BHist =>
                hsame row residualRead ∧ PkgSig bundle residualRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory residualRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffSocketResidual residualReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary dischargeSocketUnary handoffSocketResidual
  have sourceResidualRead :
      (fun row : BHist => hsame row residualRead ∧ UnaryHistory row) residualRead := by
    exact ⟨hsame_refl residualRead, residualReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row residualRead ∨
              hsame row obstruction)
          (fun row : BHist =>
            hsame row residualRead ∧ PkgSig bundle residualRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead sourceResidualRead
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, residualReadPkg, provenancePkg⟩
  }
  exact ⟨cert, residualReadUnary, provenancePkg⟩

theorem MetaCICCriticalPathResidualConfluenceRowBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName localPeak candidateJoin residualFrontier substitutionBoundary boundedChecker
      residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName localPeak →
        Cont localPeak normalForm candidateJoin →
          Cont candidateJoin obstruction residualFrontier →
            Cont residualFrontier transport substitutionBoundary →
              Cont substitutionBoundary handoff boundedChecker →
                Cont boundedChecker obstruction residualRead →
                  PkgSig bundle residualRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row localPeak ∨ hsame row candidateJoin ∨
                            hsame row residualFrontier ∨ hsame row substitutionBoundary ∨
                              hsame row boundedChecker ∨ hsame row obstruction ∨
                                hsame row residualRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle residualRead pkg ∧
                            PkgSig bundle provenance pkg ∧
                              Cont boundedChecker obstruction residualRead)
                        hsame ∧
                      UnaryHistory localPeak ∧ UnaryHistory candidateJoin ∧
                        UnaryHistory residualFrontier ∧ UnaryHistory substitutionBoundary ∧
                          UnaryHistory boundedChecker ∧ UnaryHistory residualRead ∧
                            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalPeak localPeakNormalFormCandidate candidateObstructionFrontier
    frontierTransportSubstitution substitutionHandoffChecker checkerObstructionResidual
    residualReadPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have localPeakUnary : UnaryHistory localPeak :=
    unary_cont_closed routeUnary localNameUnary routeLocalPeak
  have candidateJoinUnary : UnaryHistory candidateJoin :=
    unary_cont_closed localPeakUnary normalFormUnary localPeakNormalFormCandidate
  have residualFrontierUnary : UnaryHistory residualFrontier :=
    unary_cont_closed candidateJoinUnary obstructionUnary candidateObstructionFrontier
  have substitutionBoundaryUnary : UnaryHistory substitutionBoundary :=
    unary_cont_closed residualFrontierUnary transportUnary frontierTransportSubstitution
  have boundedCheckerUnary : UnaryHistory boundedChecker :=
    unary_cont_closed substitutionBoundaryUnary handoffUnary substitutionHandoffChecker
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed boundedCheckerUnary obstructionUnary checkerObstructionResidual
  have sourceResidualRead :
      (fun row : BHist => hsame row residualRead ∧ UnaryHistory row) residualRead := by
    exact ⟨hsame_refl residualRead, residualReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row localPeak ∨ hsame row candidateJoin ∨
              hsame row residualFrontier ∨ hsame row substitutionBoundary ∨
                hsame row boundedChecker ∨ hsame row obstruction ∨ hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle residualRead pkg ∧
              PkgSig bundle provenance pkg ∧
                Cont boundedChecker obstruction residualRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead sourceResidualRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, residualReadPkg, provenancePkg, checkerObstructionResidual⟩
  }
  exact
    ⟨cert, localPeakUnary, candidateJoinUnary, residualFrontierUnary,
      substitutionBoundaryUnary, boundedCheckerUnary, residualReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
