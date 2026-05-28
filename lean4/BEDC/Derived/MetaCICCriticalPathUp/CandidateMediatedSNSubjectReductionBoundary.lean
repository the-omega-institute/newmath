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

theorem MetaCICCriticalPathCandidateMediatedSNSubjectReductionBoundary [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead frontierReplay socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm candidateRead →
        Cont candidateRead handoff frontierReplay →
          Cont handoff obstruction socketRead →
            PkgSig bundle frontierReplay pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row obstruction ∨ hsame row dischargeSocket ∨
                      hsame row frontierReplay ∨ hsame row socketRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont handoff obstruction socketRead ∧
                      PkgSig bundle frontierReplay pkg)
                  hsame ∧
                UnaryHistory frontierReplay ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFormCandidate candidateHandoffFrontier
    handoffObstructionRead frontierReplayPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormCandidate
  have frontierReplayUnary : UnaryHistory frontierReplay :=
    unary_cont_closed candidateReadUnary handoffUnary candidateHandoffFrontier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  have sourceSocket :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row frontierReplay ∨
              hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont handoff obstruction socketRead ∧
              PkgSig bundle frontierReplay pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocket
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, handoffObstructionRead, frontierReplayPkg⟩
  }
  exact ⟨cert, frontierReplayUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
