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

theorem MetaCICCriticalPathConfluenceResidualBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route dischargeSocket residualRead ->
        PkgSig bundle residualRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row route ∨ hsame row dischargeSocket ∨ hsame row residualRead)
              (fun row : BHist =>
                hsame row residualRead ∧ PkgSig bundle residualRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory residualRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeSocketResidual residualPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed routeUnary dischargeSocketUnary routeSocketResidual
  have residualSource :
      (fun row : BHist => hsame row residualRead ∧ UnaryHistory row) residualRead := by
    exact ⟨hsame_refl residualRead, residualUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row dischargeSocket ∨ hsame row residualRead)
          (fun row : BHist =>
            hsame row residualRead ∧ PkgSig bundle residualRead pkg ∧
              PkgSig bundle provenance pkg)
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, residualPkg, provenancePkg⟩
  }
  exact ⟨cert, residualUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
