import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDecidabilityCut [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName residualRead normalizationRead frontierRead checkerRead budgetRead
      cutRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont handoff route residualRead ->
        Cont strongNorm normalForm normalizationRead ->
          Cont residualRead normalizationRead frontierRead ->
            Cont frontierRead transport checkerRead ->
              Cont checkerRead dischargeSocket budgetRead ->
                Cont budgetRead handoff cutRead ->
                  PkgSig bundle checkerRead pkg ->
                    PkgSig bundle budgetRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row cutRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row frontierRead ∨ hsame row checkerRead ∨
                              hsame row budgetRead ∨ hsame row cutRead ∨
                                hsame row dischargeSocket)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle checkerRead pkg ∧
                              PkgSig bundle budgetRead pkg)
                          hsame ∧
                        UnaryHistory residualRead ∧ UnaryHistory normalizationRead ∧
                          UnaryHistory frontierRead ∧ UnaryHistory checkerRead ∧
                            UnaryHistory budgetRead ∧ UnaryHistory cutRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffRouteResidual strongNormalNormalization residualNormalizationFrontier
    frontierTransportChecker checkerSocketBudget budgetHandoffCut checkerPkg budgetPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteResidual
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormalNormalization
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed residualUnary normalizationUnary residualNormalizationFrontier
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed frontierUnary transportUnary frontierTransportChecker
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed checkerUnary dischargeSocketUnary checkerSocketBudget
  have cutUnary : UnaryHistory cutRead :=
    unary_cont_closed budgetUnary handoffUnary budgetHandoffCut
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cutRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontierRead ∨ hsame row checkerRead ∨ hsame row budgetRead ∨
              hsame row cutRead ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle checkerRead pkg ∧
              PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cutRead ⟨hsame_refl cutRead, cutUnary⟩
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
      exact ⟨source.right, checkerPkg, budgetPkg⟩
  }
  exact
    ⟨cert, residualUnary, normalizationUnary, frontierUnary, checkerUnary, budgetUnary,
      cutUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
