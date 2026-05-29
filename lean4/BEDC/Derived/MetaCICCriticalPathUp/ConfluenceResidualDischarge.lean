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

theorem MetaCICCriticalPathConfluenceResidualDischarge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName localPeak candidateJoin residualFrontier substitutionBoundary boundedChecker
      residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
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
                            Cont boundedChecker obstruction residualRead)
                        hsame ∧
                      UnaryHistory residualRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalPeak peakNormalJoin joinObstructionFrontier
    frontierTransportBoundary boundaryHandoffChecker checkerObstructionResidual residualPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _socketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have localPeakUnary : UnaryHistory localPeak :=
    unary_cont_closed routeUnary localNameUnary routeLocalPeak
  have candidateJoinUnary : UnaryHistory candidateJoin :=
    unary_cont_closed localPeakUnary normalFormUnary peakNormalJoin
  have residualFrontierUnary : UnaryHistory residualFrontier :=
    unary_cont_closed candidateJoinUnary obstructionUnary joinObstructionFrontier
  have substitutionBoundaryUnary : UnaryHistory substitutionBoundary :=
    unary_cont_closed residualFrontierUnary transportUnary frontierTransportBoundary
  have boundedCheckerUnary : UnaryHistory boundedChecker :=
    unary_cont_closed substitutionBoundaryUnary handoffUnary boundaryHandoffChecker
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed boundedCheckerUnary obstructionUnary checkerObstructionResidual
  have residualSource :
      (fun row : BHist => hsame row residualRead ∧ UnaryHistory row) residualRead := by
    exact ⟨hsame_refl residualRead, residualUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row localPeak ∨ hsame row candidateJoin ∨
              hsame row residualFrontier ∨ hsame row substitutionBoundary ∨
                hsame row boundedChecker ∨ hsame row obstruction ∨
                  hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle residualRead pkg ∧
              Cont boundedChecker obstruction residualRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead residualSource
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
      exact ⟨source.right, residualPkg, checkerObstructionResidual⟩
  }
  exact ⟨cert, residualUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
