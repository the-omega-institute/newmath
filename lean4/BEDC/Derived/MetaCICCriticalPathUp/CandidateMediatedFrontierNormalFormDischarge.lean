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

theorem MetaCICCriticalPathCandidateMediatedFrontierNormalFormDischarge
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName frontierRead normalFormRead dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm frontierRead →
        Cont frontierRead route normalFormRead →
          Cont normalFormRead dischargeSocket dischargeRead →
            PkgSig bundle dischargeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row strongNorm ∨ hsame row normalForm ∨ hsame row route ∨
                      hsame row dischargeSocket ∨ hsame row dischargeRead)
                  (fun row : BHist =>
                    hsame row dischargeRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle dischargeRead pkg)
                  hsame ∧
                UnaryHistory frontierRead ∧ UnaryHistory normalFormRead ∧
                  UnaryHistory dischargeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFrontier frontierRouteNormalForm
    normalFormSocketDischarge dischargeReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary,
    _localNameUnary, _packetStrongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFrontier
  have normalFormReadUnary : UnaryHistory normalFormRead :=
    unary_cont_closed frontierReadUnary routeUnary frontierRouteNormalForm
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed normalFormReadUnary dischargeSocketUnary normalFormSocketDischarge
  have sourceDischarge :
      (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row) dischargeRead := by
    exact ⟨hsame_refl dischargeRead, dischargeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row route ∨
              hsame row dischargeSocket ∨ hsame row dischargeRead)
          (fun row : BHist =>
            hsame row dischargeRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle dischargeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dischargeRead sourceDischarge
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
      exact ⟨source.left, provenancePkg, dischargeReadPkg⟩
  }
  exact ⟨cert, frontierReadUnary, normalFormReadUnary, dischargeReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
