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

theorem MetaCICCriticalPathResidualSubstitutionNormalizationFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance localName
      residualRead normalizationRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont handoff route residualRead →
        Cont strongNorm normalForm normalizationRead →
          Cont residualRead normalizationRead frontierRead →
            PkgSig bundle frontierRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row residualRead ∨ hsame row normalizationRead ∨
                      hsame row obstruction ∨ hsame row dischargeSocket ∨
                        hsame row frontierRead)
                  (fun row : BHist =>
                    hsame row frontierRead ∧ PkgSig bundle frontierRead pkg ∧
                      PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory residualRead ∧ UnaryHistory normalizationRead ∧
                  UnaryHistory frontierRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffRoute strongNormal frontierRoute frontierPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary routeUnary handoffRoute
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormal
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed residualUnary normalizationUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row normalizationRead ∨ hsame row obstruction ∨
              hsame row dischargeSocket ∨ hsame row frontierRead)
          (fun row : BHist =>
            hsame row frontierRead ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
      exact ⟨source.left, frontierPkg, provenancePkg⟩
  }
  exact ⟨cert, residualUnary, normalizationUnary, frontierUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
