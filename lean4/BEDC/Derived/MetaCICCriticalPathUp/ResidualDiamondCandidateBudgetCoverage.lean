import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondCandidateBudgetCoverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance localName
      residualRead candidateRead socketRead coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont strongNorm normalForm candidateRead ->
        Cont handoff dischargeSocket residualRead ->
          Cont residualRead candidateRead socketRead ->
            Cont socketRead route coverageRead ->
              PkgSig bundle coverageRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row strongNorm ∨ hsame row handoff ∨ hsame row dischargeSocket ∨
                        hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row socketRead ∨ hsame row coverageRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont residualRead candidateRead socketRead ∧
                        Cont socketRead route coverageRead ∧ PkgSig bundle coverageRead pkg)
                    hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                  UnaryHistory socketRead ∧ UnaryHistory coverageRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet candidateRoute residualRoute socketRoute coverageRoute coveragePkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed strongNormUnary normalFormUnary candidateRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary dischargeSocketUnary residualRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary candidateUnary socketRoute
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed socketUnary routeUnary coverageRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row handoff ∨ hsame row dischargeSocket ∨
              hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
                hsame row coverageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont residualRead candidateRead socketRead ∧
              Cont socketRead route coverageRead ∧ PkgSig bundle coverageRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coverageRead ⟨hsame_refl coverageRead, coverageUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketRoute, coverageRoute, coveragePkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, socketUnary, coverageUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
