import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathParallelDiamondPublicExportRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName frontierPublic criticalPublic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName frontierPublic →
        Cont frontierPublic provenance criticalPublic →
          PkgSig bundle criticalPublic pkg →
            SemanticNameCert
                (fun row : BHist => hsame row criticalPublic ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row frontierPublic ∨ hsame row criticalPublic ∨ hsame row route ∨
                    hsame row provenance ∨ hsame row localName)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont route localName frontierPublic ∧
                    Cont frontierPublic provenance criticalPublic ∧
                      PkgSig bundle criticalPublic pkg)
                hsame ∧
              UnaryHistory frontierPublic ∧ UnaryHistory criticalPublic := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalFrontier frontierProvenanceCritical criticalPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _socketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontierPublic :=
    unary_cont_closed routeUnary localNameUnary routeLocalFrontier
  have criticalUnary : UnaryHistory criticalPublic :=
    unary_cont_closed frontierUnary provenanceUnary frontierProvenanceCritical
  have sourceCritical :
      (fun row : BHist => hsame row criticalPublic ∧ UnaryHistory row)
        criticalPublic := by
    exact ⟨hsame_refl criticalPublic, criticalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row criticalPublic ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontierPublic ∨ hsame row criticalPublic ∨ hsame row route ∨
              hsame row provenance ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName frontierPublic ∧
              Cont frontierPublic provenance criticalPublic ∧
                PkgSig bundle criticalPublic pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro criticalPublic sourceCritical
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeLocalFrontier, frontierProvenanceCritical, criticalPkg⟩
  }
  exact ⟨cert, frontierUnary, criticalUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
