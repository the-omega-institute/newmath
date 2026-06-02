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

theorem MetaCICCriticalPathL10NormalizationFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName l10Frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName l10Frontier →
        PkgSig bundle l10Frontier pkg →
          SemanticNameCert
              (fun row : BHist => hsame row l10Frontier ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                    hsame row localName ∨ hsame row l10Frontier)
              (fun row : BHist =>
                hsame row l10Frontier ∧ PkgSig bundle l10Frontier pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory l10Frontier ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalFrontier l10FrontierPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have l10FrontierUnary : UnaryHistory l10Frontier :=
    unary_cont_closed routeUnary localNameUnary routeLocalFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row l10Frontier ∧ UnaryHistory row) l10Frontier := by
    exact ⟨hsame_refl l10Frontier, l10FrontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Frontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                hsame row localName ∨ hsame row l10Frontier)
          (fun row : BHist =>
            hsame row l10Frontier ∧ PkgSig bundle l10Frontier pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro l10Frontier sourceFrontier
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, l10FrontierPkg, provenancePkg⟩
  }
  exact ⟨cert, l10FrontierUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
