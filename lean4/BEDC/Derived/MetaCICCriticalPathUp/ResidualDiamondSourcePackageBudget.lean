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

theorem MetaCICCriticalPathResidualDiamondSourcePackageBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName l10Source residualRead localDiamond packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName l10Source ->
        Cont l10Source obstruction residualRead ->
          Cont residualRead handoff localDiamond ->
            Cont localDiamond provenance packageRead ->
              PkgSig bundle packageRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row l10Source ∨ hsame row residualRead ∨
                        hsame row localDiamond ∨ hsame row packageRead ∨
                          hsame row obstruction ∨ hsame row dischargeSocket)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont l10Source obstruction residualRead ∧
                        Cont residualRead handoff localDiamond ∧
                          Cont localDiamond provenance packageRead ∧ PkgSig bundle packageRead pkg)
                    hsame ∧
                  UnaryHistory l10Source ∧ UnaryHistory residualRead ∧
                    UnaryHistory localDiamond ∧ UnaryHistory packageRead ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameSource sourceObstructionResidual residualHandoffDiamond
    diamondProvenancePackage packagePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have sourceUnary : UnaryHistory l10Source :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSource
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed sourceUnary obstructionUnary sourceObstructionResidual
  have diamondUnary : UnaryHistory localDiamond :=
    unary_cont_closed residualUnary handoffUnary residualHandoffDiamond
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed diamondUnary provenanceUnary diamondProvenancePackage
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row l10Source ∨ hsame row residualRead ∨ hsame row localDiamond ∨
              hsame row packageRead ∨ hsame row obstruction ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont l10Source obstruction residualRead ∧
              Cont residualRead handoff localDiamond ∧
                Cont localDiamond provenance packageRead ∧ PkgSig bundle packageRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro packageRead
        ⟨hsame_refl packageRead, packageUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceObstructionResidual, residualHandoffDiamond,
          diamondProvenancePackage, packagePkg⟩
  }
  exact ⟨cert, sourceUnary, residualUnary, diamondUnary, packageUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
