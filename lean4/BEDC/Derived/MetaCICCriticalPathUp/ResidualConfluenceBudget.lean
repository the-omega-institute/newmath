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

end BEDC.Derived.MetaCICCriticalPathUp
