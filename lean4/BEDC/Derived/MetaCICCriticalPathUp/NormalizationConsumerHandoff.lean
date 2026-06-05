import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathNormalizationConsumerHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont strongNorm normalForm normalRead →
        PkgSig bundle normalRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row normalRead ∨
                  hsame row obstruction ∨ hsame row dischargeSocket)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle normalRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory normalRead := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFormNormal normalPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormNormal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row normalRead ∨
              hsame row obstruction ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle normalRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normalRead ⟨hsame_refl normalRead, normalUnary⟩
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
      exact ⟨source.right, normalPkg, provenancePkg⟩
  }
  exact ⟨cert, normalUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
