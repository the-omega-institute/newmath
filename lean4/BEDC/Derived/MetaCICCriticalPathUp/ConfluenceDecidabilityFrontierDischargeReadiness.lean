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

theorem MetaCICCriticalPathConfluenceDecidabilityFrontierDischargeReadiness
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName localPeak candidateJoin residualFrontier substitutionBoundary boundedChecker
      neutralSpine socketRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont route localName localPeak →
        Cont localPeak normalForm candidateJoin →
          Cont candidateJoin obstruction residualFrontier →
            Cont residualFrontier transport substitutionBoundary →
              Cont substitutionBoundary handoff boundedChecker →
                Cont boundedChecker obstruction neutralSpine →
                  Cont neutralSpine dischargeSocket socketRead →
                    Cont socketRead provenance frontierRead →
                      PkgSig bundle frontierRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row residualFrontier ∨ hsame row boundedChecker ∨
                                hsame row obstruction ∨ hsame row dischargeSocket ∨
                                  hsame row frontierRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                                Cont socketRead provenance frontierRead)
                            hsame ∧
                          UnaryHistory frontierRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalPeak peakNormalJoin joinObstructionFrontier
    frontierTransportBoundary boundaryHandoffChecker checkerObstructionSpine
    spineSocketRead socketProvenanceFrontier frontierPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
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
  have neutralSpineUnary : UnaryHistory neutralSpine :=
    unary_cont_closed boundedCheckerUnary obstructionUnary checkerObstructionSpine
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed neutralSpineUnary dischargeSocketUnary spineSocketRead
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed socketReadUnary provenanceUnary socketProvenanceFrontier
  have frontierSource :
      (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row) frontierRead := by
    exact ⟨hsame_refl frontierRead, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualFrontier ∨ hsame row boundedChecker ∨
              hsame row obstruction ∨ hsame row dischargeSocket ∨
                hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              Cont socketRead provenance frontierRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead frontierSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, socketProvenanceFrontier⟩
  }
  exact ⟨cert, frontierUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
